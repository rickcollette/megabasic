// interpreter/interpreter.go
package interpreter

import (
    "fmt"
    "strings"

)

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
    TokGOTO2
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
    TokPlus
    TokMinus
    TokMultiply
    TokDivide
    TokPower
    TokAssign
    TokEqual
    TokNotEqual
    TokLessThan
    TokGreaterThan
    TokLessEq
    TokGreaterEq
    TokAnd
    TokOr
    TokNot

    // Delimiters
    TokComma
    TokLParen
    TokRParen
    TokColon
    TokSemicolon

    // Others
    TokEOL
)

// LoopFrame represents a loop's state.
type LoopFrame struct {
    Variable string
    End      ast.Value
    Step     ast.Value
    StartPC  int // Program counter at the start of the loop
}

// Interpreter holds the state of the BASIC interpreter.
type Interpreter struct {
    Subs           map[string]*ast.SubStatement
    Variables      map[string]ast.Value
    DataQueue      []ast.Value
    LoopStack      []*LoopFrame
    SubCallStack   []int
    Program        []ast.Statement
    ProgramCounter int
    Labels         map[string]int // For label-based GOTO
    Files          map[string]*os.File
    Memory         []byte
    MemoryInitialized bool
}

// NewInterpreter initializes the interpreter.
func NewInterpreter() *Interpreter {
    return &Interpreter{
        Subs:           make(map[string]*ast.SubStatement),
        Variables:      make(map[string]ast.Value),
        DataQueue:      []ast.Value{},
        LoopStack:      []*LoopFrame{},
        SubCallStack:   []int{},
        Program:        []ast.Statement{},
        ProgramCounter: 0,
        Labels:         make(map[string]int),
        Files:          make(map[string]*os.File),
        Memory:         nil,
        MemoryInitialized: false,
    }
}

// DefineSub registers a new subroutine.
func (interp *Interpreter) DefineSub(name string, params []string, body []ast.Statement) {
    interp.Subs[strings.ToUpper(name)] = &ast.SubStatement{
        Name:       strings.ToUpper(name),
        Parameters: params,
        Body:       body,
    }
}

// ParseProgram parses a list of program lines into the interpreter's program.
func (interp *Interpreter) ParseProgram(lines []string) error {
    for _, line := range lines {
        if strings.TrimSpace(line) == "" {
            continue // Skip empty lines
        }

        // Parse the line
        parser := NewParser(line)
        tokens, err := parser.Tokenize()
        if err != nil {
            return fmt.Errorf("Parse error: %v", err)
        }

        if len(tokens) == 0 {
            continue
        }

        // Handle labels (e.g., LABEL:)
        if tokens[0].Type == TokIdentifier && len(tokens) > 1 && tokens[1].Type == TokColon {
            label := tokens[0].Value
            interp.Labels[strings.ToUpper(label)] = len(interp.Program)
            continue
        }

        // Identify the statement type
        firstToken := tokens[0].Type
        stmtParser, exists := statementParsers[firstToken]
        if !exists {
            // Handle implicit LET if first token is identifier and next token is '='
            if tokens[0].Type == TokIdentifier && len(tokens) > 1 && tokens[1].Type == TokAssign {
                stmt, err := parseLETStatement(tokens)
                if err != nil {
                    return err
                }
                interp.Program = append(interp.Program, stmt)
                continue
            }
            return fmt.Errorf("Unsupported statement: %s", tokens[0].Value)
        }

        stmt, err := stmtParser(tokens)
        if err != nil {
            return err
        }

        interp.Program = append(interp.Program, stmt)
    }
    return nil
}

// ExecuteProgram runs the entire program.
func (interp *Interpreter) ExecuteProgram() error {
    for interp.ProgramCounter < len(interp.Program) {
        stmt := interp.Program[interp.ProgramCounter]
        err := stmt.Execute(interp)
        if err != nil {
            return fmt.Errorf("Error at statement %d: %v", interp.ProgramCounter+1, err)
        }
        interp.ProgramCounter++
    }
    return nil
}

// ExecuteSub handles the execution of a subroutine.
func (interp *Interpreter) ExecuteSub(sub *ast.SubStatement, args []ast.Value) error {
    if len(args) != len(sub.Parameters) {
        return fmt.Errorf("Sub %s expects %d arguments, got %d", sub.Name, len(sub.Parameters), len(args))
    }

    // Assign arguments to parameters
    for i, param := range sub.Parameters {
        interp.SetVariable(param, args[i])
    }

    // Push the current ProgramCounter to the call stack
    interp.SubCallStack = append(interp.SubCallStack, interp.ProgramCounter)

    // Execute subroutine body
    for _, stmt := range sub.Body {
        err := stmt.Execute(interp)
        if err != nil {
            return err
        }
    }

    // Pop the ProgramCounter from the call stack
    if len(interp.SubCallStack) == 0 {
        return fmt.Errorf("SubCallStack is empty")
    }
    returnAddr := interp.SubCallStack[len(interp.SubCallStack)-1]
    interp.SubCallStack = interp.SubCallStack[:len(interp.SubCallStack)-1]
    interp.ProgramCounter = returnAddr

    return nil
}

// FindLineNumber finds the index of a statement by its label.
func (interp *Interpreter) FindLineNumber(target string) int {
    upperTarget := strings.ToUpper(target)
    if pc, exists := interp.Labels[upperTarget]; exists {
        return pc
    }
    return -1
}

// LookupVariable retrieves a variable's value, checking the call stack for local variables.
func (interp *Interpreter) LookupVariable(name string) (ast.Value, bool) {
    upperName := strings.ToUpper(name)
    val, exists := interp.Variables[upperName]
    return val, exists
}

// SetVariable sets a variable's value, prioritizing local scope.
func (interp *Interpreter) SetVariable(name string, val ast.Value) {
    upperName := strings.ToUpper(name)
    interp.Variables[upperName] = val
}