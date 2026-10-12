// Blockchain Security Analyzer - coded by Mr Sabaz Ali Khan
//
// Defensive tooling for reviewing smart contracts and addresses:
//   contract  - static pattern analysis of Solidity source (.sol)
//   bytecode  - opcode / selector analysis of deployed runtime bytecode
//   address   - EIP-55 checksum validation, address-poisoning check, optional on-chain review
//   selftest  - verify the built-in keccak256 / checksum / opcode engines
//
// Findings are heuristics meant to guide a manual audit, not a replacement for one.
package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"math/big"
	"math/bits"
	"net/http"
	"os"
	"regexp"
	"sort"
	"strings"
	"time"
)

// ───────────────────────────── report model ─────────────────────────────

type Finding struct {
	ID       string `json:"id"`
	Severity string `json:"severity"`
	Title    string `json:"title"`
	Detail   string `json:"detail"`
	Line     int    `json:"line,omitempty"`
	Fix      string `json:"fix,omitempty"`
}

type Report struct {
	Target   string    `json:"target"`
	Kind     string    `json:"kind"`
	Score    int       `json:"risk_score"`
	Grade    string    `json:"grade"`
	Findings []Finding `json:"findings"`
	Credit   string    `json:"credit"`
}

var sevRank = map[string]int{"CRITICAL": 4, "HIGH": 3, "MEDIUM": 2, "LOW": 1, "INFO": 0}
var sevWeight = map[string]int{"CRITICAL": 25, "HIGH": 15, "MEDIUM": 8, "LOW": 3, "INFO": 0}

var useColor = true

func col(code, s string) string {
	if !useColor {
		return s
	}
	return "\033[" + code + "m" + s + "\033[0m"
}

func sevColor(s string) string {
	switch s {
	case "CRITICAL":
		return "1;41;97"
	case "HIGH":
		return "1;31"
	case "MEDIUM":
		return "33"
	case "LOW":
		return "36"
	}
	return "90"
}

func add(r *Report, id, sev, title, detail string, line int, fix string) {
	r.Findings = append(r.Findings, Finding{id, sev, title, detail, line, fix})
}

func finalize(r *Report) {
	sort.SliceStable(r.Findings, func(i, j int) bool {
		a, b := r.Findings[i], r.Findings[j]
		if sevRank[a.Severity] != sevRank[b.Severity] {
			return sevRank[a.Severity] > sevRank[b.Severity]
		}
		return a.Line < b.Line
	})
	score := 0
	for _, f := range r.Findings {
		score += sevWeight[f.Severity]
	}
	if score > 100 {
		score = 100
	}
	r.Score = score
	switch {
	case score == 0:
		r.Grade = "A"
	case score <= 10:
		r.Grade = "B"
	case score <= 30:
		r.Grade = "C"
	case score <= 60:
		r.Grade = "D"
	default:
		r.Grade = "F"
	}
	r.Credit = creditLine
}

func printReport(r *Report, asJSON bool, minSev string) {
	finalize(r)
	min := sevRank[strings.ToUpper(minSev)]
	var shown []Finding
	for _, f := range r.Findings {
		if sevRank[f.Severity] >= min {
			shown = append(shown, f)
		}
	}
	r.Findings = shown
	if asJSON {
		b, _ := json.MarshalIndent(r, "", "  ")
		fmt.Println(string(b))
		return
	}
	fmt.Printf("%s %s (%s)\n", col("1", "Target:"), r.Target, r.Kind)
	fmt.Printf("%s %d/100   %s %s\n\n", col("1", "Risk score:"), r.Score, col("1", "Grade:"), r.Grade)
	if len(r.Findings) == 0 {
		fmt.Println(col("32", "No findings at or above the selected severity."))
	}
	counts := map[string]int{}
	for i, f := range r.Findings {
		counts[f.Severity]++
		loc := ""
		if f.Line > 0 {
			loc = fmt.Sprintf("  (line %d)", f.Line)
		}
		fmt.Printf("%2d. %s %s [%s]%s\n", i+1, col(sevColor(f.Severity), " "+f.Severity+" "), f.Title, f.ID, loc)
		fmt.Printf("      %s\n", f.Detail)
		if f.Fix != "" {
			fmt.Printf("      %s %s\n", col("32", "Fix:"), f.Fix)
		}
		fmt.Println()
	}
	fmt.Printf("Summary: critical=%d high=%d medium=%d low=%d info=%d\n",
		counts["CRITICAL"], counts["HIGH"], counts["MEDIUM"], counts["LOW"], counts["INFO"])
	fmt.Printf("\n%s  -  %s\n", toolName, creditLine)
}

// ───────────────────────────── keccak-256 ─────────────────────────────

var keccakRC = [24]uint64{
	0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
	0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
	0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
	0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
	0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
	0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
}
var keccakRot = [24]int{1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44}
var keccakPi = [24]int{10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1}

func keccakF(st *[25]uint64) {
	var bc [5]uint64
	for round := 0; round < 24; round++ {
		for i := 0; i < 5; i++ {
			bc[i] = st[i] ^ st[i+5] ^ st[i+10] ^ st[i+15] ^ st[i+20]
		}
		for i := 0; i < 5; i++ {
			t := bc[(i+4)%5] ^ bits.RotateLeft64(bc[(i+1)%5], 1)
			for j := 0; j < 25; j += 5 {
				st[j+i] ^= t
			}
		}
		t := st[1]
		for i := 0; i < 24; i++ {
			j := keccakPi[i]
			b := st[j]
			st[j] = bits.RotateLeft64(t, keccakRot[i])
			t = b
		}
		for j := 0; j < 25; j += 5 {
			for i := 0; i < 5; i++ {
				bc[i] = st[j+i]
			}
			for i := 0; i < 5; i++ {
				st[j+i] ^= (^bc[(i+1)%5]) & bc[(i+2)%5]
			}
		}
		st[0] ^= keccakRC[round]
	}
}

func keccak256(data []byte) []byte {
	const rate = 136
	var st [25]uint64
	buf := append([]byte{}, data...)
	buf = append(buf, 0x01)
	for len(buf)%rate != 0 {
		buf = append(buf, 0)
	}
	buf[len(buf)-1] |= 0x80
	for off := 0; off < len(buf); off += rate {
		for i := 0; i < rate/8; i++ {
			st[i] ^= binary.LittleEndian.Uint64(buf[off+i*8:])
		}
		keccakF(&st)
	}
	out := make([]byte, 32)
	for i := 0; i < 4; i++ {
		binary.LittleEndian.PutUint64(out[i*8:], st[i])
	}
	return out
}

// ───────────────────────────── helpers ─────────────────────────────

func decodeHex(s string) ([]byte, error) {
	s = strings.Map(func(r rune) rune {
		if r == ' ' || r == '\n' || r == '\r' || r == '\t' {
			return -1
		}
		return r
	}, s)
	s = strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X")
	if len(s)%2 == 1 {
		return nil, fmt.Errorf("odd-length hex string")
	}
	return hex.DecodeString(s)
}

func checksumAddress(addr string) string {
	a := strings.ToLower(strings.TrimPrefix(strings.TrimPrefix(addr, "0x"), "0X"))
	h := hex.EncodeToString(keccak256([]byte(a)))
	out := []byte("0x")
	for i := 0; i < len(a); i++ {
		c := a[i]
		if c >= 'a' && c <= 'f' && h[i] >= '8' {
			c -= 32
		}
		out = append(out, c)
	}
	return string(out)
}

var reAddr = regexp.MustCompile(`^0[xX][0-9a-fA-F]{40}$`)

func lineOf(src string, off int) int {
	if off > len(src) {
		off = len(src)
	}
	return strings.Count(src[:off], "\n") + 1
}

func stripComments(src string) string {
	b := []byte(src)
	out := make([]byte, len(b))
	copy(out, b)
	var inStr byte
	i := 0
	for i < len(b) {
		c := b[i]
		if inStr != 0 {
			if c == '\\' {
				i += 2
				continue
			}
			if c == inStr {
				inStr = 0
			}
			i++
			continue
		}
		if c == '"' || c == '\'' {
			inStr = c
			i++
			continue
		}
		if c == '/' && i+1 < len(b) && b[i+1] == '/' {
			for i < len(b) && b[i] != '\n' {
				out[i] = ' '
				i++
			}
			continue
		}
		if c == '/' && i+1 < len(b) && b[i+1] == '*' {
			for i < len(b) && !(b[i] == '*' && i+1 < len(b) && b[i+1] == '/') {
				if b[i] != '\n' {
					out[i] = ' '
				}
				i++
			}
			if i < len(b) {
				out[i] = ' '
				i++
			}
			if i < len(b) {
				out[i] = ' '
				i++
			}
			continue
		}
		i++
	}
	return string(out)
}

func matchBrace(s string, open int) int {
	depth := 0
	for i := open; i < len(s); i++ {
		switch s[i] {
		case '{':
			depth++
		case '}':
			depth--
			if depth == 0 {
				return i
			}
		}
	}
	return len(s) - 1
}

// ───────────────────────────── Solidity analysis ─────────────────────────────

type rule struct {
	id, sev, title, detail, fix string
	re                          *regexp.Regexp
}

var solRules = []rule{
	{"SWC-115", "HIGH", "tx.origin used", "tx.origin-based checks can be abused by a malicious intermediary contract (phishing-style call chains).", "Use msg.sender for authorization.", regexp.MustCompile(`\btx\.origin\b`)},
	{"SWC-112", "HIGH", "delegatecall in use", "delegatecall runs foreign code with this contract's storage; a controllable target means full takeover.", "Restrict targets to immutable, audited implementations and gate access strictly.", regexp.MustCompile(`\.delegatecall\s*\(`)},
	{"SWC-106", "HIGH", "selfdestruct present", "A reachable selfdestruct lets the contract be destroyed and its balance swept.", "Remove it, or guard behind multi-sig/timelock governance.", regexp.MustCompile(`\b(selfdestruct|suicide)\s*\(`)},
	{"SWC-107", "HIGH", "Legacy .call.value() pattern", "Old-style value call forwards all gas and is a classic reentrancy vector.", "Use checks-effects-interactions plus ReentrancyGuard.", regexp.MustCompile(`\.call\.value\s*\(`)},
	{"SWC-107", "MEDIUM", "Low-level call", "Low-level calls forward control flow to an external party; review for reentrancy and return-value handling.", "Prefer pull-payments; apply nonReentrant and check the returned bool.", regexp.MustCompile(`\.call\s*(\{[^}]*\})?\s*\(`)},
	{"SWC-111", "LOW", "Deprecated Solidity construct", "throw / sha3 / callcode are deprecated and removed in modern compilers.", "Use revert(), keccak256(), delegatecall.", regexp.MustCompile(`\bthrow\s*;|\bsha3\s*\(|\bcallcode\b`)},
	{"SWC-116", "LOW", "Timestamp dependence", "block.timestamp can be nudged by validators; unsafe for tight deadlines or randomness.", "Avoid sub-minute precision and never use it as an entropy source.", regexp.MustCompile(`\bblock\.timestamp\b|\bnow\b`)},
	{"SWC-120", "MEDIUM", "Weak randomness source", "blockhash / difficulty / prevrandao are predictable or influenceable by block producers.", "Use a verifiable randomness oracle (e.g. VRF) or commit-reveal.", regexp.MustCompile(`\bblockhash\s*\(|\bblock\.(difficulty|prevrandao)\b`)},
	{"SWC-103", "LOW", "Floating pragma", "A floating compiler version lets the contract be built with untested compiler releases.", "Pin an exact, audited compiler version.", regexp.MustCompile(`pragma\s+solidity\s*\^`)},
	{"SWC-101", "MEDIUM", "Pre-0.8 compiler (no overflow checks)", "Solidity < 0.8 does not revert on integer overflow/underflow.", "Upgrade to >=0.8 or use SafeMath consistently.", regexp.MustCompile(`pragma\s+solidity\s*[\^>=<~ ]*0\.[0-7]\.\d+`)},
	{"SWC-127", "INFO", "Inline assembly", "Assembly bypasses compiler safety checks and needs manual review.", "Keep blocks minimal and document invariants.", regexp.MustCompile(`\bassembly\b\s*(\([^)]*\))?\s*\{`)},
	{"SWC-117", "MEDIUM", "ecrecover usage", "Raw ecrecover returns address(0) on bad signatures and signatures can be malleable.", "Use OpenZeppelin ECDSA, reject address(0), and bind nonces/chainId in the signed data.", regexp.MustCompile(`\becrecover\s*\(`)},
	{"SWC-134", "LOW", "transfer()/send() with fixed 2300 gas", "Fixed gas stipends break when recipient gas costs change.", "Use call{value:} with reentrancy protection.", regexp.MustCompile(`\.(transfer|send)\s*\(\s*[^,)]+\)`)},
	{"SWC-132", "MEDIUM", "Strict equality on contract balance", "Forced ETH (selfdestruct) can break balance == checks.", "Track deposits in an internal accounting variable.", regexp.MustCompile(`==\s*address\(this\)\.balance|address\(this\)\.balance\s*==`)},
	{"SWC-128", "LOW", "Unbounded loop over dynamic array", "Loops over growing arrays can exceed the block gas limit (DoS).", "Paginate or use pull-based accounting.", regexp.MustCompile(`for\s*\([^;]*;[^;]*\.length\s*;`)},
	{"SWC-133", "INFO", "abi.encodePacked", "encodePacked with multiple dynamic types can create hash collisions.", "Use abi.encode for hashed/signed multi-field data.", regexp.MustCompile(`abi\.encodePacked\s*\(`)},
	{"INFO-UNCHK", "INFO", "unchecked arithmetic block", "unchecked disables overflow protection inside the block.", "Confirm bounds are provably safe.", regexp.MustCompile(`\bunchecked\s*\{`)},
	{"INFO-ADDR", "INFO", "Hard-coded address", "Hard-coded addresses reduce flexibility and can hide backdoors.", "Verify each address and prefer constructor/immutable config.", regexp.MustCompile(`\b0x[0-9a-fA-F]{40}\b`)},
}

var (
	reFunc      = regexp.MustCompile(`function\s+(\w+)\s*\(([^)]*)\)([^{;]*)\{`)
	reUnchecked = regexp.MustCompile(`^\s*[\w\.\[\]\(\)]+\.(call|send|delegatecall|staticcall)\b`)
	reACMod     = regexp.MustCompile(`\b(onlyOwner|onlyRole|onlyAdmin|onlyGovernance|onlyOperator|auth|requiresAuth|initializer|reinitializer|only[A-Z]\w*)\b`)
	reHighNames = regexp.MustCompile(`(?i)^(transferOwnership|changeOwner|setOwner|mint\w*|upgrade\w*|kill|destroy|drain|sweep\w*|rescue\w*|withdrawAll|emergency\w*)$`)
	reCall      = regexp.MustCompile(`\.call\s*(\{[^}]*\})?\s*\(|\.call\.value\s*\(`)
	reStateWr   = regexp.MustCompile(`\w+(\[[^\]]+\])+\s*([+\-*/]?=)[^=]|\b\w+\s*[+\-]=`)
)

func scanSolidity(path string) (*Report, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	src := stripComments(string(raw))
	r := &Report{Target: path, Kind: "solidity-source"}

	// Pattern rules (capped per rule to keep reports readable).
	for _, ru := range solRules {
		n := 0
		for _, m := range ru.re.FindAllStringIndex(src, -1) {
			add(r, ru.id, ru.sev, ru.title, ru.detail, lineOf(src, m[0]), ru.fix)
			if n++; n >= 25 {
				break
			}
		}
	}

	// Unchecked low-level call return values.
	for i, ln := range strings.Split(src, "\n") {
		if reUnchecked.MatchString(ln) && strings.Contains(ln, ";") {
			add(r, "SWC-104", "MEDIUM", "Unchecked low-level call return value",
				"The success flag of a low-level call is ignored; failures pass silently.",
				i+1, "Capture the bool and require() it.")
		}
	}

	// Function-level heuristics.
	for _, m := range reFunc.FindAllStringSubmatchIndex(src, -1) {
		name := src[m[2]:m[3]]
		header := src[m[6]:m[7]]
		open := m[1] - 1
		end := matchBrace(src, open)
		body := src[open : end+1]
		line := lineOf(src, m[0])

		if strings.Contains(header, "internal") || strings.Contains(header, "private") ||
			strings.Contains(header, " view") || strings.Contains(header, " pure") {
			continue
		}
		hasAC := reACMod.MatchString(header) ||
			strings.Contains(body, "msg.sender") || strings.Contains(body, "_msgSender()") ||
			strings.Contains(body, "hasRole") || strings.Contains(body, "_checkOwner")

		if !hasAC && (strings.Contains(body, "selfdestruct") || strings.Contains(body, ".delegatecall")) {
			add(r, "SWC-106/112", "CRITICAL", "Unprotected destructive/delegating function",
				fmt.Sprintf("%s() is externally reachable, has no visible access control, and uses selfdestruct/delegatecall.", name),
				line, "Add an access-control modifier (onlyOwner / role check).")
		}
		if !hasAC && reHighNames.MatchString(name) {
			add(r, "SWC-105", "HIGH", "Privileged function without access control",
				fmt.Sprintf("%s() looks privileged but no modifier or msg.sender check was found.", name),
				line, "Gate with onlyOwner/onlyRole or equivalent.")
		}
		if (strings.EqualFold(name, "initialize") || strings.EqualFold(name, "init")) && !strings.Contains(header, "initializer") {
			add(r, "SWC-118", "HIGH", "Initializer may be re-callable",
				fmt.Sprintf("%s() has no initializer guard; anyone may be able to (re)initialize and seize ownership.", name),
				line, "Use OpenZeppelin Initializable's initializer modifier.")
		}
		// Reentrancy: state write after an external call.
		if loc := reCall.FindStringIndex(body); loc != nil && !strings.Contains(header, "nonReentrant") {
			if reStateWr.MatchString(body[loc[1]:]) {
				add(r, "SWC-107", "HIGH", "State change after external call (reentrancy risk)",
					fmt.Sprintf("%s() updates state after a low-level call and is not marked nonReentrant.", name),
					lineOf(src, open+loc[0]), "Apply checks-effects-interactions and add nonReentrant.")
			}
		}
	}

	finalizeDedupe(r)
	return r, nil
}

func finalizeDedupe(r *Report) {
	seen := map[string]bool{}
	var out []Finding
	for _, f := range r.Findings {
		k := fmt.Sprintf("%s|%s|%d", f.ID, f.Title, f.Line)
		if !seen[k] {
			seen[k] = true
			out = append(out, f)
		}
	}
	r.Findings = out
}

// ───────────────────────────── bytecode analysis ─────────────────────────────

var opNames = map[byte]string{
	0xff: "SELFDESTRUCT", 0xf4: "DELEGATECALL", 0xf2: "CALLCODE", 0xf1: "CALL",
	0xf0: "CREATE", 0xf5: "CREATE2", 0x32: "ORIGIN", 0x42: "TIMESTAMP",
	0x40: "BLOCKHASH", 0x44: "PREVRANDAO/DIFFICULTY", 0x55: "SSTORE",
}

var knownSelectors = map[string]string{
	"a9059cbb": "transfer(address,uint256)", "095ea7b3": "approve(address,uint256)",
	"23b872dd": "transferFrom(address,address,uint256)", "40c10f19": "mint(address,uint256)",
	"8456cb59": "pause()", "3f4ba83a": "unpause()", "f2fde38b": "transferOwnership(address)",
	"715018a6": "renounceOwnership()", "3659cfe6": "upgradeTo(address)",
	"4f1ef286": "upgradeToAndCall(address,bytes)", "8da5cb5b": "owner()", "5c60da1b": "implementation()",
}

func analyzeBytecode(r *Report, code []byte) {
	if len(code) == 0 {
		add(r, "BC-EMPTY", "INFO", "No runtime code",
			"Address is an EOA, undeployed, or a self-destructed contract.", 0, "")
		return
	}
	counts := map[byte]int{}
	sels := map[string]bool{}
	for i := 0; i < len(code); {
		op := code[i]
		if _, ok := opNames[op]; ok {
			counts[op]++
		}
		if op == 0x63 && i+4 < len(code) { // PUSH4: possible function selector
			s := hex.EncodeToString(code[i+1 : i+5])
			if _, ok := knownSelectors[s]; ok {
				sels[s] = true
			}
		}
		if op >= 0x60 && op <= 0x7f {
			i += int(op-0x5f) + 1
		} else {
			i++
		}
	}
	add(r, "BC-SIZE", "INFO", "Runtime bytecode size",
		fmt.Sprintf("%d bytes, keccak256 code hash 0x%s", len(code), hex.EncodeToString(keccak256(code))), 0, "")

	if bytes.HasPrefix(code, []byte{0x36, 0x3d, 0x3d, 0x37, 0x3d, 0x3d, 0x3d, 0x36, 0x3d, 0x73}) {
		add(r, "BC-PROXY", "MEDIUM", "EIP-1167 minimal proxy",
			"Behaviour is defined entirely by the implementation contract it delegates to.", 0,
			"Audit the implementation address embedded in the bytecode.")
	}
	type chk struct {
		op       byte
		sev, msg string
		fix      string
	}
	for _, c := range []chk{
		{0xff, "HIGH", "SELFDESTRUCT opcode present", "Contract can be destroyed; confirm it is unreachable or tightly governed."},
		{0xf2, "HIGH", "CALLCODE opcode present", "Deprecated and dangerous; indicates very old or hand-written code."},
		{0x32, "HIGH", "ORIGIN opcode present", "tx.origin is used somewhere; check it is not used for authorization."},
		{0xf4, "MEDIUM", "DELEGATECALL opcode present", "Proxy/library pattern; verify who controls the delegate target."},
		{0xf5, "MEDIUM", "CREATE2 opcode present", "Deterministic deployment; check for metamorphic (redeployable) contract tricks."},
		{0x44, "LOW", "PREVRANDAO/DIFFICULTY opcode present", "If used as randomness it is influenceable."},
		{0x40, "LOW", "BLOCKHASH opcode present", "If used as randomness it is predictable."},
		{0x42, "LOW", "TIMESTAMP opcode present", "Check for timestamp-dependent logic."},
	} {
		if n := counts[c.op]; n > 0 {
			add(r, "BC-"+opNames[c.op], c.sev, c.msg, fmt.Sprintf("%d occurrence(s). Heuristic: constant data may produce false positives.", n), 0, c.fix)
		}
	}
	var names []string
	for s := range sels {
		names = append(names, knownSelectors[s])
	}
	sort.Strings(names)
	if len(names) > 0 {
		add(r, "BC-SELECTORS", "INFO", "Notable function selectors",
			strings.Join(names, ", ")+" - review who may call privileged ones (mint, pause, upgrade, ownership).", 0, "")
	}
}

// ───────────────────────────── JSON-RPC ─────────────────────────────

func rpcCall(url, method string, params ...interface{}) (string, error) {
	if params == nil {
		params = []interface{}{}
	}
	payload, _ := json.Marshal(map[string]interface{}{"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
	client := &http.Client{Timeout: 20 * time.Second}
	resp, err := client.Post(url, "application/json", bytes.NewReader(payload))
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}
	var out struct {
		Result string `json:"result"`
		Error  *struct {
			Message string `json:"message"`
		} `json:"error"`
	}
	if err := json.Unmarshal(body, &out); err != nil {
		return "", err
	}
	if out.Error != nil {
		return "", fmt.Errorf("rpc error: %s", out.Error.Message)
	}
	return out.Result, nil
}

const eip1967ImplSlot = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"

func onChain(r *Report, rpc, addr string) {
	codeHex, err := rpcCall(rpc, "eth_getCode", addr, "latest")
	if err != nil {
		add(r, "RPC-ERR", "LOW", "RPC query failed", err.Error(), 0, "Check the endpoint URL and network access.")
		return
	}
	code, err := decodeHex(codeHex)
	if err != nil {
		add(r, "RPC-ERR", "LOW", "Could not decode code", err.Error(), 0, "")
		return
	}
	analyzeBytecode(r, code)
	if id, err := rpcCall(rpc, "eth_chainId"); err == nil {
		if n, ok := new(big.Int).SetString(strings.TrimPrefix(id, "0x"), 16); ok {
			add(r, "RPC-CHAIN", "INFO", "Chain ID", n.String(), 0, "")
		}
	}
	if bal, err := rpcCall(rpc, "eth_getBalance", addr, "latest"); err == nil {
		if wei, ok := new(big.Int).SetString(strings.TrimPrefix(bal, "0x"), 16); ok {
			eth := new(big.Float).Quo(new(big.Float).SetInt(wei), big.NewFloat(1e18))
			add(r, "RPC-BAL", "INFO", "Native balance", eth.Text('f', 6)+" (native units)", 0, "")
		}
	}
	if v, err := rpcCall(rpc, "eth_getStorageAt", addr, eip1967ImplSlot, "latest"); err == nil {
		t := strings.TrimLeft(strings.TrimPrefix(v, "0x"), "0")
		if t != "" {
			if len(t) < 40 {
				t = strings.Repeat("0", 40-len(t)) + t
			}
			add(r, "RPC-PROXY", "MEDIUM", "EIP-1967 upgradeable proxy",
				"Implementation: 0x"+t+". The logic can be swapped by whoever controls the admin.", 0,
				"Verify the admin is a multi-sig/timelock and audit the implementation.")
		}
	}
}

// ───────────────────────────── commands ─────────────────────────────

type common struct {
	asJSON, noColor, noBanner *bool
	minSev                    *string
}

func addCommon(fs *flag.FlagSet) common {
	return common{
		asJSON:   fs.Bool("json", false, "output JSON"),
		noColor:  fs.Bool("nocolor", false, "disable ANSI colours"),
		noBanner: fs.Bool("nobanner", false, "hide banner"),
		minSev:   fs.String("min", "info", "minimum severity: info|low|medium|high|critical"),
	}
}

func (c common) start() {
	useColor = !*c.noColor && os.Getenv("NO_COLOR") == ""
	if !*c.asJSON && !*c.noBanner {
		printBanner()
	}
}

func fatal(err error) {
	fmt.Fprintln(os.Stderr, "error:", err)
	os.Exit(1)
}

func cmdContract(args []string) {
	fs := flag.NewFlagSet("contract", flag.ExitOnError)
	file := fs.String("f", "", "Solidity file to analyze")
	c := addCommon(fs)
	fs.Parse(args)
	if *file == "" {
		fs.Usage()
		os.Exit(2)
	}
	c.start()
	r, err := scanSolidity(*file)
	if err != nil {
		fatal(err)
	}
	printReport(r, *c.asJSON, *c.minSev)
}

func cmdBytecode(args []string) {
	fs := flag.NewFlagSet("bytecode", flag.ExitOnError)
	hx := fs.String("hex", "", "runtime bytecode as hex")
	file := fs.String("f", "", "file containing runtime bytecode hex")
	rpc := fs.String("rpc", "", "JSON-RPC endpoint (use with -a)")
	addr := fs.String("a", "", "contract address (use with -rpc)")
	c := addCommon(fs)
	fs.Parse(args)
	c.start()
	r := &Report{Kind: "bytecode"}
	switch {
	case *rpc != "" && *addr != "":
		r.Target = *addr
		onChain(r, *rpc, *addr)
	case *hx != "" || *file != "":
		s := *hx
		r.Target = "inline-hex"
		if *file != "" {
			b, err := os.ReadFile(*file)
			if err != nil {
				fatal(err)
			}
			s, r.Target = string(b), *file
		}
		code, err := decodeHex(s)
		if err != nil {
			fatal(err)
		}
		analyzeBytecode(r, code)
	default:
		fs.Usage()
		os.Exit(2)
	}
	printReport(r, *c.asJSON, *c.minSev)
}

func cmdAddress(args []string) {
	fs := flag.NewFlagSet("address", flag.ExitOnError)
	addr := fs.String("a", "", "address to check")
	cmp := fs.String("compare", "", "address you intended to use (address-poisoning check)")
	rpc := fs.String("rpc", "", "optional JSON-RPC endpoint for on-chain review")
	c := addCommon(fs)
	fs.Parse(args)
	if *addr == "" {
		fs.Usage()
		os.Exit(2)
	}
	c.start()
	r := &Report{Target: *addr, Kind: "address"}
	a := *addr
	if !reAddr.MatchString(a) {
		add(r, "ADDR-FMT", "CRITICAL", "Invalid address format", "Expected 0x followed by 40 hex characters.", 0, "Re-copy the address from a trusted source.")
		printReport(r, *c.asJSON, *c.minSev)
		return
	}
	body := a[2:]
	lower := strings.ToLower(body)
	switch {
	case body != lower && body != strings.ToUpper(body):
		if checksumAddress(a) == "0x"+body {
			add(r, "ADDR-CS", "INFO", "EIP-55 checksum valid", "Mixed-case checksum verified.", 0, "")
		} else {
			add(r, "ADDR-CS", "HIGH", "EIP-55 checksum mismatch",
				"Likely typo or tampering. Correct form: "+checksumAddress(a), 0, "Do not send funds until the address is verified.")
		}
	default:
		add(r, "ADDR-CS", "LOW", "No checksum protection", "Single-case address cannot detect typos. Checksummed: "+checksumAddress(a), 0, "Use the checksummed form.")
	}
	if strings.Trim(lower, "0") == "" {
		add(r, "ADDR-ZERO", "HIGH", "Zero address", "Funds sent here are unrecoverable.", 0, "")
	}
	if lower == "000000000000000000000000000000000000dead" {
		add(r, "ADDR-BURN", "INFO", "Well-known burn address", "Tokens sent here are effectively destroyed.", 0, "")
	}
	if strings.HasPrefix(lower, strings.Repeat("0", 38)) && lower[38:] != "00" && lower[38:] <= "09" {
		add(r, "ADDR-PRE", "INFO", "Precompile address", "Reserved EVM precompile range.", 0, "")
	}
	if *cmp != "" {
		if !reAddr.MatchString(*cmp) {
			add(r, "ADDR-CMP", "MEDIUM", "Comparison address invalid", "The -compare value is not a valid address.", 0, "")
		} else {
			x, y := strings.ToLower(a[2:]), strings.ToLower((*cmp)[2:])
			switch {
			case x == y:
				add(r, "ADDR-CMP", "INFO", "Matches intended address", "Both addresses are identical.", 0, "")
			case x[:4] == y[:4] && x[len(x)-4:] == y[len(y)-4:]:
				add(r, "ADDR-POISON", "CRITICAL", "Possible address poisoning",
					"First and last characters match the intended address but the middle differs - a known look-alike scam pattern.", 0,
					"Compare the FULL address; never copy from transaction history.")
			default:
				add(r, "ADDR-CMP", "HIGH", "Different from intended address", "The addresses do not match.", 0, "")
			}
		}
	}
	if *rpc != "" {
		onChain(r, *rpc, a)
	}
	printReport(r, *c.asJSON, *c.minSev)
}

func cmdSelftest() {
	ok := true
	check := func(name string, pass bool) {
		status := col("32", "PASS")
		if !pass {
			status, ok = col("31", "FAIL"), false
		}
		fmt.Printf("  [%s] %s\n", status, name)
	}
	check("keccak256(\"\")", hex.EncodeToString(keccak256(nil)) == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
	check("keccak256(\"abc\")", hex.EncodeToString(keccak256([]byte("abc"))) == "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")
	check("EIP-55 checksum vector", checksumAddress("0x5aaeb6053f3e94c9b9a09f33669435e7ef1beaed") == "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed")
	r := &Report{}
	analyzeBytecode(r, []byte{0x60, 0xff, 0xff}) // PUSH1 0xff must NOT count as SELFDESTRUCT, trailing 0xff must
	n := 0
	for _, f := range r.Findings {
		if f.ID == "BC-SELFDESTRUCT" {
			n++
		}
	}
	check("opcode walker skips PUSH data", n == 1)
	if !ok {
		os.Exit(1)
	}
}

func usage() {
	printBanner()
	fmt.Println(`Usage:
  bsa contract -f Token.sol [-json] [-min medium]
  bsa bytecode -hex 0x6080... | -f code.hex | -rpc <url> -a <contract>
  bsa address  -a 0x... [-compare 0x...] [-rpc <url>]
  bsa selftest

Common flags: -json  -nocolor  -nobanner  -min info|low|medium|high|critical`)
}

func main() {
	if len(os.Args) < 2 {
		usage()
		os.Exit(2)
	}
	switch os.Args[1] {
	case "contract":
		cmdContract(os.Args[2:])
	case "bytecode":
		cmdBytecode(os.Args[2:])
	case "address":
		cmdAddress(os.Args[2:])
	case "selftest":
		printBanner()
		cmdSelftest()
	default:
		usage()
		os.Exit(2)
	}
}
