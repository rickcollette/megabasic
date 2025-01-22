package parser

import (
    "fmt"
    "unicode"
)

// --------------------------------------------------------------------
// 1) Define the set of parse instructions (the “bytecode”).
// --------------------------------------------------------------------

// We mimic something like the parser bytecode in "parserbytecode.s".
// Each instruction is an integer code. In the 6502 code, these were
// small opcodes in the range $00-$1F. We define them in Go:

type ParseInstr int

const (
    // Basic instructions
    PAI_FAIL ParseInstr = iota      // $00
    PAI_ACCEPT                      // $01
    PAI_TRYSTATEMENT                // $02
    PAI_OR                          // $03
    PAI_EOL                         // $04
    PAI_B                           // $05 (unconditional branch)
    PAI_BEQ                         // $06 (branch if match)
    PAI_EMIT                        // $07
    PAI_COPYLINE                    // $08
    PAI_RTS                         // $09
    PAI_TRYNUMBER                   // $0A
    PAI_TRYVARIABLE                 // $0B
    PAI_TRYFUNCTION                 // $0C
    PAI_HEX_B                       // $0D
    PAI_STEND                       // $0E
    PAI_STRING                      // $0F
    PAI_BSTR                        // $10
    PAI_NUM                         // $11
    PAI_STR                         // $12
    PAI_EMIT_B                      // $13
    PAI_TRYARRAYVAR                 // $14
    PAI_BEOS                        // $15
    PAI_ENDIF                       // $16

    // For convenience: partial expansions or placeholders for future instructions
    // ...
)

// --------------------------------------------------------------------
// 2) Define the states used in "parserbytecode.s" (like pa_state0, pa_expr...).
//    We'll keep them as constants or an enum.
// --------------------------------------------------------------------
type ParseState int

const (
    PST_STATE0 ParseState = iota
    PST_STATE1
    PST_EXPR
    PST_AEXPR
    PST_SEXPR
    PST_AVAR
    PST_IOCB
    PST_ARRAY
    PST_ARRAY2
    PST_COMMA
    PST_AEXPR_COMMA
    PST_LET
    PST_OPENFUN
    PST_AEXPR_NEXT
    // ... add more states as needed
)

// --------------------------------------------------------------------
// 3) Data structures for tokens, parse output, etc.
// --------------------------------------------------------------------

// TokenType represents the type of lexical tokens.
type TokenType int

const (
    // Special tokens
    TokEOF TokenType = iota
    TokUnknown

    // Literals
    TokNumber
    TokString
    TokIdentifier

    // Keywords
    TokSUB
    TokENDSUB
    TokRETURN
    TokIF
    TokTHEN
    TokELSE
    TokENDIF
    TokFOR
    TokNEXT
    TokGOTO
    TokGOTO2        // Possibly for different GOTO syntax
    TokGOSUB
    TokTRAP
    TokBYE
    TokCONT
    TokCOM
    TokCLOSE
    TokCLR
    TokDEG
    TokDIM
    TokEND
    TokNEW
    TokOPEN
    TokLOAD
    TokSAVE
    TokSTATUS
    TokNOTE
    TokPOINT
    TokXIO
    TokON
    TokPOKE
    TokPRINT
    TokRAD
    TokREAD
    TokRESTORE
    TokRUN
    TokSTOP
    TokPOP
    TokGET
    TokPUT
    TokGRAPHICS
    TokPLOT
    TokPOSITION
    TokDOS
    TokDRAWTO
    TokSETCOLOR
    TokLOCATE
    TokSOUND
    TokLPRINT
    TokCSAVE
    TokCLOAD
    TokRENAME
    TokMOVE
    TokMISSILE
    TokPMCLR
    TokPMCOLOR
    TokPMGRAPHICS
    TokPMMOVE

    // Additional Keywords
    TokDATA
    TokINPUT
    TokLET
    TokWHILE
    TokWEND
    TokTRACE
    TokTRACEOFF
    TokDEL
    TokRPUT
    TokRGET
    TokBPUT
    TokBGET
    TokTAB
    TokCP
    TokERASE
    TokPROTECT
    TokUNPROTECT
    TokDIR
    TokLOMEM

    // Operators
    TokPlus       // +
    TokMinus      // -
    TokMultiply   // *
    TokDivide     // /
    TokPower      // ^
    TokAssign     // =
    TokEqual      // ==
    TokNotEqual   // <>
    TokLessThan   // <
    TokGreaterThan// >
    TokLessEq     // <=
    TokGreaterEq  // >=
    TokAnd        // AND
    TokOr         // OR
    TokNot        // NOT

    // Delimiters
    TokComma     // ,
    TokLParen    // (
    TokRParen    // )
    TokColon     // :
    TokSemicolon // ;

    // Others
    TokEOL // End of Line
)


type Token struct {
    Type  TokenType
    Value string
}

// ParseResult is what we get after parsing a line: a slice of tokens, or an error
type ParseResult struct {
    Tokens []Token
    Err    error
}

// --------------------------------------------------------------------
// 4) The Parser object itself
// --------------------------------------------------------------------

type Parser struct {
    input string   // The line we're parsing
    pos   int      // current index in input
    ch    rune     // current character
    tokens []Token // where we store parsed tokens

    // We can keep a “state” stack or single “currentState” here:
    currentState ParseState
}

// StatementParser defines a function type for parsing statements.
type StatementParser func(p *Parser) (Statement, error)

// statementParsers maps TokenTypes to their respective parsing functions.
var statementParsers = map[TokenType]StatementParser{
    TokREM:        parseREM,
    TokDATA:       parseDATA,
    TokINPUT:      parseINPUT,
    TokLET:        parseLET,
    TokPRINT:      parsePRINT,
    TokIF:         parseIF,
    TokFOR:        parseFOR,
    TokNEXT:       parseNEXT,
    TokGOTO:       parseGOTO,
    TokGOTO2:      parseGOTO2,
    TokGOSUB:      parseGOSUB,
    TokTRAP:       parseTRAP,
    TokBYE:        parseBYE,
    TokCONT:       parseCONT,
    TokCOM:        parseCOM,
    TokCLOSE:      parseCLOSE,
    TokCLR:        parseCLR,
    TokDEG:        parseDEG,
    TokDIM:        parseDIM,
    TokEND:        parseEND,
    TokNEW:        parseNEW,
    TokOPEN:       parseOPEN,
    TokLOAD:       parseLOAD,
    TokSAVE:       parseSAVE,
    TokSTATUS:     parseSTATUS,
    TokNOTE:       parseNOTE,
    TokPOINT:      parsePOINT,
    TokXIO:        parseXIO,
    TokON:         parseON,
    TokPOKE:       parsePOKE,
    TokRAD:        parseRAD,
    TokREAD:       parseREAD,
    TokRESTORE:    parseRESTORE,
    TokRUN:        parseRUN,
    TokSTOP:       parseSTOP,
    TokPOP:        parsePOP,
    TokGET:        parseGET,
    TokPUT:        parsePUT,
    TokGRAPHICS:   parseGRAPHICS,
    TokPLOT:       parsePLOT,
    TokPOSITION:   parsePOSITION,
    TokDOS:        parseDOS,
    TokDRAWTO:     parseDRAWTO,
    TokSETCOLOR:   parseSETCOLOR,
    TokLOCATE:     parseLOCATE,
    TokSOUND:      parseSOUND,
    TokLPRINT:     parseLPRINT,
    TokCSAVE:      parseCSAVE,
    TokCLOAD:      parseCLOAD,
    TokRENAME:     parseRENAME,
    TokMOVE:       parseMOVE,
    TokMISSILE:    parseMISSILE,
    TokPMCLR:      parsePMCLR,
    TokPMCOLOR:    parsePMCOLOR,
    TokPMGRAPHICS: parsePMGRAPHICS,
    TokPMMOVE:     parsePMMOVE,
    TokWHILE:      parseWHILE,
    TokWEND:       parseWEND,
    TokTRACE:      parseTRACE,
    TokTRACEOFF:   parseTRACEOFF,
    TokDEL:        parseDEL,
    TokRPUT:       parseRPUT,
    TokRGET:       parseRGET,
    TokBPUT:       parseBPUT,
    TokBGET:       parseBGET,
    TokTAB:        parseTAB,
    TokCP:         parseCP,
    TokERASE:      parseERASE,
    TokPROTECT:    parsePROTECT,
    TokUNPROTECT:  parseUNPROTECT,
    TokDIR:        parseDIR,
    TokLOMEM:      parseLOMEM,
    // Add more as needed
}

func LookupKeyword(word string) TokenType {
    switch word {
    case "SUB":
        return TokSUB
    case "END SUB":
        return TokENDSUB
    case "RETURN":
        return TokRETURN
    case "IF":
        return TokIF
    case "THEN":
        return TokTHEN
    case "ELSE":
        return TokELSE
    case "ENDIF":
        return TokENDIF
    case "FOR":
        return TokFOR
    case "NEXT":
        return TokNEXT
    case "GOTO":
        return TokGOTO
    case "GOTO2":
        return TokGOTO2
    case "GOSUB":
        return TokGOSUB
    case "TRAP":
        return TokTRAP
    case "BYE":
        return TokBYE
    case "CONT":
        return TokCONT
    case "COM":
        return TokCOM
    case "CLOSE":
        return TokCLOSE
    case "CLR":
        return TokCLR
    case "DEG":
        return TokDEG
    case "DIM":
        return TokDIM
    case "END":
        return TokEND
    case "NEW":
        return TokNEW
    case "OPEN":
        return TokOPEN
    case "LOAD":
        return TokLOAD
    case "SAVE":
        return TokSAVE
    case "STATUS":
        return TokSTATUS
    case "NOTE":
        return TokNOTE
    case "POINT":
        return TokPOINT
    case "XIO":
        return TokXIO
    case "ON":
        return TokON
    case "POKE":
        return TokPOKE
    case "PRINT":
        return TokPRINT
    case "RAD":
        return TokRAD
    case "READ":
        return TokREAD
    case "RESTORE":
        return TokRESTORE
    case "RUN":
        return TokRUN
    case "STOP":
        return TokSTOP
    case "POP":
        return TokPOP
    case "GET":
        return TokGET
    case "PUT":
        return TokPUT
    case "GRAPHICS":
        return TokGRAPHICS
    case "PLOT":
        return TokPLOT
    case "POSITION":
        return TokPOSITION
    case "DOS":
        return TokDOS
    case "DRAWTO":
        return TokDRAWTO
    case "SETCOLOR":
        return TokSETCOLOR
    case "LOCATE":
        return TokLOCATE
    case "SOUND":
        return TokSOUND
    case "LPRINT":
        return TokLPRINT
    case "CSAVE":
        return TokCSAVE
    case "CLOAD":
        return TokCLOAD
    case "RENAME":
        return TokRENAME
    case "MOVE":
        return TokMOVE
    case "MISSILE":
        return TokMISSILE
    case "PMCLR":
        return TokPMCLR
    case "PMCOLOR":
        return TokPMCOLOR
    case "PMGRAPHICS":
        return TokPMGRAPHICS
    case "PMMOVE":
        return TokPMMOVE
    case "DATA":
        return TokDATA
    case "INPUT":
        return TokINPUT
    case "LET":
        return TokLET
    case "WHILE":
        return TokWHILE
    case "WEND":
        return TokWEND
    case "TRACE":
        return TokTRACE
    case "TRACEOFF":
        return TokTRACEOFF
    case "DEL":
        return TokDEL
    case "RPUT":
        return TokRPUT
    case "RGET":
        return TokRGET
    case "BPUT":
        return TokBPUT
    case "BGET":
        return TokBGET
    case "TAB":
        return TokTAB
    case "CP":
        return TokCP
    case "ERASE":
        return TokERASE
    case "PROTECT":
        return TokPROTECT
    case "UNPROTECT":
        return TokUNPROTECT
    case "DIR":
        return TokDIR
    case "LOMEM":
        return TokLOMEM
    default:
        return TokIdentifier
    }
}

// NewParser constructs a Parser with an input line
func NewParser(line string) *Parser {
    p := &Parser{input: line, pos: -1}
    p.advance()
    return p
}

// advance moves pos forward by 1 and updates p.ch
func (p *Parser) advance() {
    p.pos++
    if p.pos < len(p.input) {
        p.ch = rune(p.input[p.pos])
    } else {
        p.ch = 0 // sentinel
    }
}

// currentChar returns the current rune or 0 if we are at the end
func (p *Parser) currentChar() rune {
    return p.ch
}

// addToken appends a token to the parser's token list
func (p *Parser) addToken(t TokenType, val string) {
    p.tokens = append(p.tokens, Token{Type: t, Value: val})
}

// --------------------------------------------------------------------
// 5) The main parse entry method
// --------------------------------------------------------------------

// ParseLine mimics _parseLine from the original code but in Go style
func (p *Parser) ParseLine() ParseResult {
    // Typically you'd have a loop reading tokens or applying the
    // parse bytecode until you reach EOL or fail
    // We'll do a simplified approach that reads words and tries to classify them

    for p.ch != 0 {
        if unicode.IsSpace(p.ch) {
            // skip spaces
            p.skipWhitespace()
            continue
        }
        if unicode.IsDigit(p.ch) {
            num := p.parseNumber()
            p.addToken(TokNumber, num)
            continue
        }
        if p.ch == '"' {
            strVal := p.parseString()
            p.addToken(TokString, strVal)
            continue
        }
        if unicode.IsLetter(p.ch) {
            ident := p.parseIdentifier()
            // We might check if ident is a known statement (like PRINT, IF, etc.)
            // or treat as user variable. For now, treat all as identifiers.
            p.addToken(TokIdentifier, ident)
            continue
        }
        // if we have punctuation or unknown char, we might handle that too
        // ...
        // fallback
        p.advance()
    }

    // at end, push EOL token
    p.addToken(TokEOL, "")
    return ParseResult{Tokens: p.tokens, Err: nil}
}

func (p *Parser) skipWhitespace() {
    for unicode.IsSpace(p.ch) {
        p.advance()
    }
}

func (p *Parser) parseNumber() string {
    start := p.pos
    for unicode.IsDigit(p.ch) {
        p.advance()
    }
    // possibly allow decimal, exponent, hex, etc.
    return p.input[start:p.pos]
}

func (p *Parser) parseString() string {
    // assume p.ch == '"'
    p.advance() // skip the opening quote
    start := p.pos
    for p.ch != 0 && p.ch != '"' {
        p.advance()
    }
    val := p.input[start:p.pos]
    if p.ch == '"' {
        p.advance() // skip closing quote
    }
    return val
}

func (p *Parser) parseIdentifier() string {
    start := p.pos
    for unicode.IsLetter(p.ch) || unicode.IsDigit(p.ch) || p.ch == '_' {
        p.advance()
    }
    return p.input[start:p.pos]
}

// --------------------------------------------------------------------
// 6) Optionally replicate the “bytecode dispatch” approach
// --------------------------------------------------------------------
// If you want a table that references each parse instruction, you could do:

type ParseInstruction struct {
    Instr  ParseInstr
    Operand string // Could store offsets or other data
    // ...
}

// You might store a series of instructions that your parser runs:
var parserProgram = []ParseInstruction{
    {PAI_TRYSTATEMENT, ""},
    {PAI_EOL, ""},
    // etc...
}

// A hypothetical “runParserBytecode” method:
func (p *Parser) runParserBytecode(program []ParseInstruction) error {
    pc := 0
    for pc < len(program) {
        instr := program[pc]
        switch instr.Instr {
        case PAI_FAIL:
            return fmt.Errorf("Parser fail at pc=%d", pc)
        case PAI_EOL:
            p.addToken(TokEOL, "")
            return nil
        case PAI_TRYSTATEMENT:
            // you’d do something like parse a statement token
            // or we can jump to a subroutine
            // ...
            pc++
        // handle other instructions similarly
        default:
            pc++
        }
    }
    return nil
}
// parseREM parses the REM statement.
func parseREM(p *Parser) (Statement, error) {
    // REM syntax: REM [comment]
    // Everything after REM is considered a comment and ignored.

    // Collect the rest of the line as a comment.
    comment := ""
    for !p.currentTokenIs(TokEOL) {
        comment += p.currentToken().Value + " "
        p.nextToken()
    }
    comment = strings.TrimSpace(comment)

    return &REMStatement{Comment: comment}, nil
}

// REMStatement represents a REM comment.
type REMStatement struct {
    Comment string
}

func (r *REMStatement) Execute(interp *Interpreter) error {
    // REM statements do nothing during execution.
    return nil
}

// parseDATA parses the DATA statement.
func parseDATA(p *Parser) (Statement, error) {
    // DATA syntax: DATA value1, value2, ...

    dataValues := []Value{}

    p.nextToken() // Skip 'DATA'

    for !p.currentTokenIs(TokEOL) {
        tok := p.currentToken()
        switch tok.Type {
        case TokNumber:
            num, err := strconv.ParseFloat(tok.Value, 64)
            if err != nil {
                return nil, fmt.Errorf("Invalid number in DATA: %s", tok.Value)
            }
            dataValues = append(dataValues, Value{Num: num})
        case TokString:
            dataValues = append(dataValues, Value{Str: tok.Value, IsStr: true})
        default:
            return nil, fmt.Errorf("Invalid DATA value: %s", tok.Value)
        }
        p.nextToken()

        if p.currentTokenIs(TokComma) {
            p.nextToken() // Skip comma
        }
    }

    return &DATAStatement{Values: dataValues}, nil
}

// DATAStatement represents a DATA statement.
type DATAStatement struct {
    Values []Value
}

func (d *DATAStatement) Execute(interp *Interpreter) error {
    // DATA statements are processed during the READ statement.
    // They can be stored in a data queue or similar structure.
    interp.DataQueue = append(interp.DataQueue, d.Values...)
    return nil
}

// parseINPUT parses the INPUT statement.
func parseINPUT(p *Parser) (Statement, error) {
    // INPUT syntax: INPUT "prompt", variable1, variable2, ...

    prompt := ""
    variables := []string{}

    p.nextToken() // Skip 'INPUT'

    // Optional prompt
    if p.currentTokenIs(TokString) {
        prompt = p.currentToken().Value
        p.nextToken()
    }

    // Collect variables
    for !p.currentTokenIs(TokEOL) {
        if p.currentTokenIs(TokComma) {
            p.nextToken() // Skip comma
            continue
        }
        if p.currentToken().Type != TokIdentifier {
            return nil, fmt.Errorf("Expected variable name in INPUT statement")
        }
        variables = append(variables, p.currentToken().Value)
        p.nextToken()
    }

    return &INPUTStatement{Prompt: prompt, Variables: variables}, nil
}

// INPUTStatement represents an INPUT statement.
type INPUTStatement struct {
    Prompt    string
    Variables []string
}

func (i *INPUTStatement) Execute(interp *Interpreter) error {
    if i.Prompt != "" {
        fmt.Print(i.Prompt)
    }

    for _, varName := range i.Variables {
        var input string
        _, err := fmt.Scanln(&input)
        if err != nil {
            return fmt.Errorf("Failed to read input for variable %s", varName)
        }

        // Attempt to parse as number; if fails, treat as string.
        num, err := strconv.ParseFloat(input, 64)
        if err != nil {
            interp.SetVariable(varName, Value{Str: input, IsStr: true})
        } else {
            interp.SetVariable(varName, Value{Num: num})
        }
    }

    return nil
}

// parseLET parses the LET statement.
func parseLET(p *Parser) (Statement, error) {
    // LET syntax: LET variable = expression

    p.nextToken() // Skip 'LET'

    if !p.currentTokenIs(TokIdentifier) {
        return nil, fmt.Errorf("Expected variable name after LET")
    }

    varName := p.currentToken().Value
    p.nextToken()

    if !p.currentTokenIs(TokAssign) {
        return nil, fmt.Errorf("Expected '=' after variable name in LET statement")
    }
    p.nextToken() // Skip '='

    expr, err := p.ParseExpression()
    if err != nil {
        return nil, err
    }

    return &LETStatement{Variable: varName, Expr: expr}, nil
}

// LETStatement represents a LET statement.
type LETStatement struct {
    Variable string
    Expr     Expression
}

func (l *LETStatement) Execute(interp *Interpreter) error {
    val, err := l.Expr.Evaluate(interp)
    if err != nil {
        return err
    }
    interp.SetVariable(l.Variable, val)
    return nil
}
// parsePRINT parses the PRINT statement.
func parsePRINT(p *Parser) (Statement, error) {
    // PRINT syntax: PRINT [expression1], [expression2], ...

    expressions := []Expression{}
    separator := ","

    p.nextToken() // Skip 'PRINT'

    for !p.currentTokenIs(TokEOL) {
        if p.currentTokenIs(TokComma, TokSemicolon) {
            sepTok := p.currentToken()
            if sepTok.Type == TokComma {
                separator = ","
            } else {
                separator = ";"
            }
            p.nextToken()
            continue
        }

        expr, err := p.ParseExpression()
        if err != nil {
            return nil, err
        }
        expressions = append(expressions, expr)
    }

    return &PRINTStatement{Expressions: expressions, Separator: separator}, nil
}

// PRINTStatement represents a PRINT statement.
type PRINTStatement struct {
    Expressions []Expression
    Separator   string // "," or ";"
}

func (p *PRINTStatement) Execute(interp *Interpreter) error {
    var outputs []string
    for _, expr := range p.Expressions {
        val, err := expr.Evaluate(interp)
        if err != nil {
            return err
        }
        outputs = append(outputs, val.String())
    }

    sep := " "
    if p.Separator == "," {
        sep = "\t"
    } else if p.Separator == ";" {
        sep = ""
    }

    fmt.Print(strings.Join(outputs, sep))
    fmt.Println() // Newline after PRINT
    return nil
}

// parseIF parses the IF statement.
func parseIF(p *Parser) (Statement, error) {
    // IF condition THEN statement ELSE statement ENDIF
    // Support both single-line and block IF statements.

    p.nextToken() // Skip 'IF'

    condition, err := p.ParseExpression()
    if err != nil {
        return nil, err
    }

    if !p.currentTokenIs(TokTHEN) {
        return nil, fmt.Errorf("Expected THEN after IF condition")
    }
    p.nextToken() // Skip 'THEN'

    // Parse the THEN branch
    thenStmt, err := p.parseSingleStatement()
    if err != nil {
        return nil, err
    }

    var elseStmt Statement
    if p.currentTokenIs(TokELSE) {
        p.nextToken() // Skip 'ELSE'
        elseStmt, err = p.parseSingleStatement()
        if err != nil {
            return nil, err
        }
    }

    // Optionally handle ENDIF for block IF
    if p.currentTokenIs(TokENDIF) {
        p.nextToken() // Skip 'ENDIF'
    }

    return &IFStatement{
        Condition: condition,
        ThenBranch: thenStmt,
        ElseBranch: elseStmt,
    }, nil
}

// IFStatement represents an IF statement.
type IFStatement struct {
    Condition   Expression
    ThenBranch  Statement
    ElseBranch  Statement // Can be nil
}

func (i *IFStatement) Execute(interp *Interpreter) error {
    condVal, err := i.Condition.Evaluate(interp)
    if err != nil {
        return err
    }

    if condVal.Num != 0 {
        if i.ThenBranch != nil {
            return i.ThenBranch.Execute(interp)
        }
    } else {
        if i.ElseBranch != nil {
            return i.ElseBranch.Execute(interp)
        }
    }

    return nil
}

// parseSingleStatement parses a single statement, used in IF THEN and ELSE branches.
func (p *Parser) parseSingleStatement() (Statement, error) {
    tok := p.currentToken()
    parserFunc, exists := statementParsers[tok.Type]
    if !exists {
        return nil, fmt.Errorf("Unsupported statement in IF branch: %v", tok)
    }
    stmt, err := parserFunc(p)
    if err != nil {
        return nil, err
    }
    return stmt, nil
}

// parseFOR parses the FOR statement.
func parseFOR(p *Parser) (Statement, error) {
    // FOR variable = start TO end [STEP step]
    p.nextToken() // Skip 'FOR'

    if !p.currentTokenIs(TokIdentifier) {
        return nil, fmt.Errorf("Expected variable name in FOR statement")
    }
    varName := p.currentToken().Value
    p.nextToken() // Skip variable

    if !p.currentTokenIs(TokAssign) {
        return nil, fmt.Errorf("Expected '=' in FOR statement")
    }
    p.nextToken() // Skip '='

    startExpr, err := p.ParseExpression()
    if err != nil {
        return nil, err
    }

    if !p.currentTokenIs(TokTO) {
        return nil, fmt.Errorf("Expected TO in FOR statement")
    }
    p.nextToken() // Skip 'TO'

    endExpr, err := p.ParseExpression()
    if err != nil {
        return nil, err
    }

    stepExpr := &NumberLiteral{Value: 1} // Default STEP is 1
    if p.currentTokenIs(TokSTEP) {
        p.nextToken() // Skip 'STEP'
        stepExpr, err = p.ParseExpression()
        if err != nil {
            return nil, err
        }
    }

    return &FORStatement{
        Variable: varName,
        Start:    startExpr,
        End:      endExpr,
        Step:     stepExpr,
    }, nil
}

// FORStatement represents a FOR loop.
type FORStatement struct {
    Variable string
    Start    Expression
    End      Expression
    Step     Expression
}

func (f *FORStatement) Execute(interp *Interpreter) error {
    startVal, err := f.Start.Evaluate(interp)
    if err != nil {
        return err
    }
    endVal, err := f.End.Evaluate(interp)
    if err != nil {
        return err
    }
    stepVal, err := f.Step.Evaluate(interp)
    if err != nil {
        return err
    }

    interp.SetVariable(f.Variable, startVal)

    loop := &LoopFrame{
        Variable: f.Variable,
        End:      endVal,
        Step:     stepVal,
        // You may need to track loop boundaries and body
    }
    interp.LoopStack = append(interp.LoopStack, loop)

    return nil
}

// LoopFrame represents a loop's state.
type LoopFrame struct {
    Variable string
    End      Value
    Step     Value
}

// parseNEXT parses the NEXT statement.
func parseNEXT(p *Parser) (Statement, error) {
    // NEXT [variable]
    p.nextToken() // Skip 'NEXT'

    varName := ""
    if p.currentToken().Type == TokIdentifier {
        varName = p.currentToken().Value
        p.nextToken()
    }

    return &NEXTStatement{Variable: varName}, nil
}

// NEXTStatement represents a NEXT statement.
type NEXTStatement struct {
    Variable string // Can be empty to refer to the most recent loop
}

func (n *NEXTStatement) Execute(interp *Interpreter) error {
    if len(interp.LoopStack) == 0 {
        return fmt.Errorf("NEXT without matching FOR")
    }

    loop := interp.LoopStack[len(interp.LoopStack)-1]

    if n.Variable != "" && strings.ToUpper(n.Variable) != strings.ToUpper(loop.Variable) {
        return fmt.Errorf("NEXT variable %s does not match FOR variable %s", n.Variable, loop.Variable)
    }

    currentVal, exists := interp.LookupVariable(loop.Variable)
    if !exists {
        return fmt.Errorf("Variable %s not defined in NEXT", loop.Variable)
    }

    newVal := Value{Num: currentVal.Num + loop.Step.Num}
    interp.SetVariable(loop.Variable, newVal)

    // Check loop condition
    if (loop.Step.Num > 0 && newVal.Num <= loop.End.Num) ||
        (loop.Step.Num < 0 && newVal.Num >= loop.End.Num) {
        // Continue loop
        // Implement loop body execution, possibly using a loop counter or program counter
        // For simplicity, assume loop body is already on the program stack
        return nil
    }

    // Exit loop
    interp.LoopStack = interp.LoopStack[:len(interp.LoopStack)-1]
    return nil
}

// Example: parseGOTO parses the GOTO statement.
func parseGOTO(p *Parser) (Statement, error) {
    // GOTO lineNumber or label
    p.nextToken() // Skip 'GOTO'

    if !p.currentTokenIs(TokNumber, TokIdentifier) {
        return nil, fmt.Errorf("Expected line number or label after GOTO")
    }

    target := p.currentToken().Value
    p.nextToken()

    return &GOTOStatement{Target: target}, nil
}

// GOTOStatement represents a GOTO statement.
type GOTOStatement struct {
    Target string // Line number as string or label name
}

func (g *GOTOStatement) Execute(interp *Interpreter) error {
    // Implement GOTO logic: change program counter to target line
    // This requires managing a program counter or similar mechanism
    return fmt.Errorf("GOTO not implemented")
}

