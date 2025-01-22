// ast/ast.go
package ast

import (
	"fmt"
	"math"
	"strconv"
	"strings"

	"github.com/rickcollette/megabasic/interpreter"
)

// ASTNode represents any node in the Abstract Syntax Tree.
type ASTNode interface{}

// Statement represents a single statement in BASIC.
type Statement interface {
    ASTNode
    Execute(*interpreter.Interpreter) error
}

// Expression represents an expression in BASIC.
type Expression interface {
    ASTNode
    Evaluate(*interpreter.Interpreter) (Value, error)
}

// Value represents a BASIC value (number or string).
type Value struct {
    Num   float64
    Str   string
    IsStr bool
}

func (v Value) String() string {
    if v.IsStr {
        return v.Str
    }
    return strconv.FormatFloat(v.Num, 'f', -1, 64)
}

// BinaryOp represents a binary operation (e.g., addition, subtraction).
type BinaryOp struct {
    Op    interpreter.TokenType
    Left  Expression
    Right Expression
}

func (b *BinaryOp) Evaluate(interp *interpreter.Interpreter) (Value, error) {
    left, err := b.Left.Evaluate(interp)
    if err != nil {
        return Value{}, err
    }
    right, err := b.Right.Evaluate(interp)
    if err != nil {
        return Value{}, err
    }

    // Handle string operations
    if left.IsStr || right.IsStr {
        return handleStringOperations(b.Op, left, right)
    }

    // Perform numeric operations
    var result float64
    switch b.Op {
    case interpreter.TokPlus:
        result = left.Num + right.Num
    case interpreter.TokMinus:
        result = left.Num - right.Num
    case interpreter.TokMultiply:
        result = left.Num * right.Num
    case interpreter.TokDivide:
        if right.Num == 0 {
            return Value{}, fmt.Errorf("Division by zero")
        }
        result = left.Num / right.Num
    case interpreter.TokPower:
        result = mathPow(left.Num, right.Num)
    case interpreter.TokEqual:
        if left.Num == right.Num {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokNotEqual:
        if left.Num != right.Num {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokLessThan:
        if left.Num < right.Num {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokGreaterThan:
        if left.Num > right.Num {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokLessEq:
        if left.Num <= right.Num {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokGreaterEq:
        if left.Num >= right.Num {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokAnd:
        if (left.Num != 0) && (right.Num != 0) {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    case interpreter.TokOr:
        if (left.Num != 0) || (right.Num != 0) {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    default:
        return Value{}, fmt.Errorf("Unsupported operator: %v", b.Op)
    }

    return Value{Num: result}, nil
}

// UnaryOp represents a unary operation (e.g., negation).
type UnaryOp struct {
    Op   interpreter.TokenType
    Expr Expression
}

func (u *UnaryOp) Evaluate(interp *interpreter.Interpreter) (Value, error) {
    expr, err := u.Expr.Evaluate(interp)
    if err != nil {
        return Value{}, err
    }

    if u.Op == interpreter.TokMinus {
        if expr.IsStr {
            return Value{}, fmt.Errorf("Cannot negate a string")
        }
        return Value{Num: -expr.Num}, nil
    }

    if u.Op == interpreter.TokNot {
        if expr.Num == 0 {
            return Value{Num: 1}, nil
        }
        return Value{Num: 0}, nil
    }

    return Value{}, fmt.Errorf("Unsupported unary operator: %v", u.Op)
}

// NumberLiteral represents a numeric literal.
type NumberLiteral struct {
    Value float64
}

func (n *NumberLiteral) Evaluate(interp *interpreter.Interpreter) (Value, error) {
    return Value{Num: n.Value}, nil
}

// StringLiteral represents a string literal.
type StringLiteral struct {
    Value string
}

func (s *StringLiteral) Evaluate(interp *interpreter.Interpreter) (Value, error) {
    return Value{Str: s.Value, IsStr: true}, nil
}

// Identifier represents a variable or function call.
type Identifier struct {
    Name string
    Args []Expression // For function calls
}

func (id *Identifier) Evaluate(interp *interpreter.Interpreter) (Value, error) {
    // Check if it's a function call
    if len(id.Args) > 0 {
        // Function call
        sub, exists := interp.Subs[strings.ToUpper(id.Name)]
        if !exists {
            return Value{}, fmt.Errorf("Undefined function: %s", id.Name)
        }

        if len(id.Args) != len(sub.Parameters) {
            return Value{}, fmt.Errorf("Function %s expects %d arguments, got %d", id.Name, len(sub.Parameters), len(id.Args))
        }

        // Evaluate arguments
        args := []interpreter.Value{}
        for _, argExpr := range id.Args {
            val, err := argExpr.Evaluate(interp)
            if err != nil {
                return Value{}, err
            }
            args = append(args, val)
        }

        // Execute subroutine
        err := interp.ExecuteSub(sub, args)
        if err != nil {
            return Value{}, err
        }

        // Handle return values
        // Assume return value is stored in RET variable
        retVal, exists := interp.Variables["RET"]
        if !exists {
            return Value{}, fmt.Errorf("Function %s did not return a value", id.Name)
        }

        return retVal, nil
    }

    // Variable lookup
    varName := strings.ToUpper(id.Name)
    val, exists := interp.LookupVariable(varName)
    if !exists {
        return Value{}, fmt.Errorf("Undefined variable: %s", id.Name)
    }
    return val, nil
}

// REMStatement represents a REM comment.
type REMStatement struct {
    Comment string
}

func (r *REMStatement) Execute(interp *interpreter.Interpreter) error {
    // REM statements do nothing during execution.
    return nil
}

// DATAStatement represents a DATA statement.
type DATAStatement struct {
    Values []interpreter.Value
}

func (d *DATAStatement) Execute(interp *interpreter.Interpreter) error {
    // Append DATA values to the interpreter's data queue.
    interp.DataQueue = append(interp.DataQueue, d.Values...)
    return nil
}

// INPUTStatement represents an INPUT statement.
type INPUTStatement struct {
    Prompt    string
    Variables []string
}

func (i *INPUTStatement) Execute(interp *interpreter.Interpreter) error {
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
            interp.SetVariable(varName, interpreter.Value{Str: input, IsStr: true})
        } else {
            interp.SetVariable(varName, interpreter.Value{Num: num})
        }
    }

    return nil
}

// LETStatement represents a LET statement.
type LETStatement struct {
    Variable string
    Expr     Expression
}

func (l *LETStatement) Execute(interp *interpreter.Interpreter) error {
    val, err := l.Expr.Evaluate(interp)
    if err != nil {
        return err
    }
    interp.SetVariable(l.Variable, val)
    return nil
}

// PRINTStatement represents a PRINT statement.
type PRINTStatement struct {
    Expressions []Expression
    Separator   string // "," or ";"
}

func (p *PRINTStatement) Execute(interp *interpreter.Interpreter) error {
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

// IFStatement represents an IF statement.
type IFStatement struct {
    Condition   Expression
    ThenBranch  Statement
    ElseBranch  Statement // Can be nil
}

func (i *IFStatement) Execute(interp *interpreter.Interpreter) error {
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

// FORStatement represents a FOR loop.
type FORStatement struct {
    Variable string
    Start    Expression
    End      Expression
    Step     Expression
}

func (f *FORStatement) Execute(interp *interpreter.Interpreter) error {
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

    interp.SetVariable(f.Variable, interpreter.Value{Num: startVal.Num})

    loop := &interpreter.LoopFrame{
        Variable: f.Variable,
        End:      endVal,
        Step:     stepVal,
        StartPC:  interp.ProgramCounter + 1,
    }
    interp.LoopStack = append(interp.LoopStack, loop)

    return nil
}

// NEXTStatement represents a NEXT statement.
type NEXTStatement struct {
    Variable string // Can be empty to refer to the most recent loop
}

func (n *NEXTStatement) Execute(interp *interpreter.Interpreter) error {
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

    newVal := interpreter.Value{Num: currentVal.Num + loop.Step.Num}
    interp.SetVariable(loop.Variable, newVal)

    // Check loop condition
    if (loop.Step.Num > 0 && newVal.Num <= loop.End.Num) ||
        (loop.Step.Num < 0 && newVal.Num >= loop.End.Num) {
        // Continue loop: set ProgramCounter to StartPC
        interp.ProgramCounter = loop.StartPC
        return nil
    }

    // Exit loop
    interp.LoopStack = interp.LoopStack[:len(interp.LoopStack)-1]
    return nil
}

// GOTOStatement represents a GOTO statement.
type GOTOStatement struct {
    Target string // Line number as string or label name
}

func (g *GOTOStatement) Execute(interp *interpreter.Interpreter) error {
    targetPC := interp.FindLineNumber(g.Target)
    if targetPC == -1 {
        return fmt.Errorf("GOTO target not found: %s", g.Target)
    }
    interp.ProgramCounter = targetPC
    return nil
}

// GOSUBStatement represents a GOSUB statement.
type GOSUBStatement struct {
    Target string // Line number as string or label name
}

func (g *GOSUBStatement) Execute(interp *interpreter.Interpreter) error {
    // Push the return address (current ProgramCounter +1) onto a call stack
    interp.SubCallStack = append(interp.SubCallStack, interp.ProgramCounter+1)

    // Change ProgramCounter to target line
    targetPC := interp.FindLineNumber(g.Target)
    if targetPC == -1 {
        return fmt.Errorf("GOSUB target not found: %s", g.Target)
    }
    interp.ProgramCounter = targetPC
    return nil
}

// ReturnStatement represents a RETURN statement.
type ReturnStatement struct{}

func (r *ReturnStatement) Execute(interp *interpreter.Interpreter) error {
    if len(interp.SubCallStack) == 0 {
        return fmt.Errorf("RETURN without matching GOSUB")
    }

    // Pop the return address from the call stack
    returnAddr := interp.SubCallStack[len(interp.SubCallStack)-1]
    interp.SubCallStack = interp.SubCallStack[:len(interp.SubCallStack)-1]

    // Set ProgramCounter to return address
    interp.ProgramCounter = returnAddr
    return nil
}

// LabelStatement represents a label in the program.
type LabelStatement struct {
    Label string
}

func (l *LabelStatement) Execute(interp *interpreter.Interpreter) error {
    // Labels do not execute any action.
    return nil
}

// Additional statement types can be defined similarly...

// Helper function to handle string operations.
func handleStringOperations(op interpreter.TokenType, left, right interpreter.Value) (Value, error) {
    switch op {
    case interpreter.TokPlus:
        if left.IsStr && right.IsStr {
            return Value{Str: left.Str + right.Str, IsStr: true}, nil
        }
        return Value{}, fmt.Errorf("Type mismatch: cannot concatenate number and string")
    case interpreter.TokEqual:
        if left.IsStr && right.IsStr {
            if left.Str == right.Str {
                return Value{Num: 1}, nil
            }
            return Value{Num: 0}, nil
        }
        return Value{}, fmt.Errorf("Type mismatch: cannot compare number and string")
    case interpreter.TokNotEqual:
        if left.IsStr && right.IsStr {
            if left.Str != right.Str {
                return Value{Num: 1}, nil
            }
            return Value{Num: 0}, nil
        }
        return Value{}, fmt.Errorf("Type mismatch: cannot compare number and string")
    default:
        return Value{}, fmt.Errorf("Unsupported string operator: %v", op)
    }
}

// mathPow wraps math.Pow to allow mocking or modification if needed.
func mathPow(a, b float64) float64 {
    return math.Pow(a, b)
}