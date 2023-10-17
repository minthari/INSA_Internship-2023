#Testing CTL
#The code defines classes and functions for working with logical expressions in Computation Tree Logic (CTL).
#CTL is a branching-time temporal logic that allows reasoning about the possible future states of a system.

#The code defines two main types of operations: binary operations (BinOP) and unary operations (UOP).
#Binary operations include And, Or, and Implies, while unary operations include Not, EX, EU, AU, AX, AG, EG, AF, and EF.
#EU,AU and EX are the minimalist sets in CTL

# φ::= x |¬φ | φ∧ψ | ∋0φ | ∋[φ⋃ψ] | ∀[φ⋃ψ]

from dataclasses import dataclass
@dataclass
class TRUE:
    symb = "T"

T = TRUE()
@dataclass
class FALSE:
    symb = "F"

# Define classes for binary operators (And, Or, Implies, AU, EU, Equivalence)
@dataclass
class BinOP:
    l:object
    r:object

class And(BinOP):
    symb = "&"

class Or(BinOP):
    symb = "|"

class Implies(BinOP):
    symb = "=>"

class AU(BinOP):
    symb = "AU"

class EU(BinOP):
    symb = "EU"

class Equivalence(BinOP):
    symb = "<=>"

## Define classes for unary operators (Not, EX, AX, AG, EG, AF, EF)
@dataclass
class UOP:
    f: object
class Not(UOP):
    symb = "-"
class EX(UOP):
    symb = "EX"
class AX(UOP):
    symb = "AX"
class AG(UOP):
    symb = "AG"
class EG(UOP):
    symb = "EG"
class AF(UOP):
    symb = "AF"
class EF(UOP):
    symb = "EF"

#recursively converts a CTL formula to a string.
def fstr(f):
    print("fstr", f)
    match f:
        case TRUE() | FALSE(): return f.symb
        case str():
            return f
        case UOP(x):
            return f"{f.symb}{fstr(x)}"
        case BinOP(l, r):
            return f"({fstr(l)} {f.symb} {fstr(r)})"
        case _:
            raise ValueError(f)

#recursively removes implications from a formula, replacing them with their equivalent CTL representation.
def rmimp(f):
    match f:
        case str():
            return f
        case Implies(l, r):
            return Or(Not(rmimp(l)), rmimp(r))
        case Equivalence(l, r):
            return And(Implies(rmimp(l), rmimp(r)), Implies(rmimp(r), rmimp(l)))
        case BinOP(l, r):
            return type(f)(rmimp(l), rmimp(r))
        case UOP(x):
            return type(f)(rmimp(x))
        case _:
            raise ValueError(f)

# Add a function to implement the simplifications
def simplify(f):
    z = simplify
    match f:
        case EF(x):
            return EU(T, z(x))
        case AF(x):
            return AU(T, z(x))
        case EG(x):
            return Not(AF(Not(z(x))))
        case AG(x):
            return Not(EF(Not(z(x))))
        case AX(x):
            return Not(EX(Not(z(x))))
        case Implies(l, r):
            return Or(Not(rmimp(l)), rmimp(r))
        case Equivalence(l, r):
            return And(Implies(rmimp(l), rmimp(r)), Implies(rmimp(r), rmimp(l)))
        case BinOP(l, r):
            return type(f)(z(l), z(r))
        case UOP(x):
            return type(f)(z(x))
        case _:
            return f

def fixpoint(f):
    def ff(x):
        r = f(x)
        print(r)
        if x == r: return x
        return ff(r)
    return ff
#simplify = fixpoint(simplify)
#def f(x): return x//2
#print(fixpoint(f)(4))

# Example usage:Test cases _____________________________________________________________________________________________
#f = And(Or(Not("A"), And(Implies("B", "C"), Implies("C", "B"))), Or(Not("D"), "E"))
#assert simplify(AX(TRUE())) == Not(EX(Not(TRUE())))# AXφ=¬EX¬φ

f = And(Or(Not(And("A", Equivalence("B", "C"))), Or(Not(Implies("D", "E")), And(Not("F"), EU("G", "H")))), And(AX(AF("I")), EG(Or(And(Not(Implies("J", "K")), EU("L", AG("M"))), And(EF("N"), AU(Or("O", EG("P")), Equivalence("Q", Not("R"))))))))
f = Or(And(Not(AX(Or("A", "B"))), EU(EG("C"), AG(Not("D")))),And(Not(EF(Implies("E", "F"))), AG(AU("G", EF("H")))))
f = Or(And(EX(Or("A", Not("B"))), AU(EG("C"), EF("D"))), And(Not(EG(Implies("E", "F"))), AF(AU("G", EF("H")))))
f = And(Or(Not(AX(AU("A", "B"))), AU(EG(Implies("C", "D")), EF(Or("E", "F")))), And(Not(EG(Or("G", "H"))), AG(EU("I", Equivalence("J", "K")))))






print(fstr(f))
print(fstr(rmimp(f)))
print(fstr(simplify(f)))

# Example usage:Test cases | checked____________________________________________________________________________________
#f = Implies("x", Or("y", "z"))
#f = Not(Implies("x", Or("y", "z")))
#f = And("x", Not("y"))
#f = AG(Implies(Not("p"), EF(And("q", "r"))))
#f = EG(EU("x", AG("y")))
#f = EG(EU("a", "b"))
#f = AF(EG(Implies("p", "q")))
#f = EU(AX("a"), AG(Or("b", "c")))
#f = EU(AX("a"), AG(EF("b", "c")))
#f = AU(AG("p"), EF(Or("q", "r")))
#f = AU(AG("a"), EG(EU("b", "c")))
#f = AU(AG("p"), EF(Or("q", "r")))
#f = AU(Not(AG("x")), EU(AX("y"), AG(Or("z", "w"))))
#f = AU(AX("a"), EU(Not(AG(Or("b", "c"))), AF("d")))
#f = AU(Or(AX("x"), EG("y")), EF(Not(AG("z"))))
#f = AU(AX("a"), EU(Not(AG(Or("b", "c"))), AF("d")))
#f = AU(EF("a", "b"), EG(And("c", "d")))
#f = AG(Implies(AG(EU("x", AF("y"))), Implies("x","z")))
#f = AG(Implies(AG(EU("x", AF("y"))), Implies("x","z")))
#f = And(Implies("A", Equivalence("B" , "C")), Implies("D", "E"))
#f = And(Implies("A", Equivalence("B" , "C")), Implies("D", "E"))
#f = And(Or(Not("A"), Equivalence("B" , "C")), Or(Not("D"), "E"))
#f = AG(Implies(AG(EU("x", AF("y"))), Implies("x","z")))

#assert simplify(AG(TRUE())) == Not(EF(Not(TRUE())))# AGφ=¬EF¬φ
#assert rmimp(Not(Implies("x", "y"))), Not(Or(Not("x"), "y"))
#assert rmimp(Not(Implies("x", "y"))) == Not( Or(Not("x"), "y"))
#assert rmimp(Implies("x", And("y", "z"))), Or(Not("x"), And("y", "z"))
#assert rmimp(AX(Implies("x", "y"))), AX(Or(Not("x"), "y"))
#assert rmimp(EU("x", "y")), EU("x", "y")
#assert simplify(EF(TRUE())) == EU(TRUE(), TRUE())# EFφ=True E⋃ φ
#assert simplify(AF(TRUE())) == AU(TRUE(), TRUE())# AFφ=True A⋃ φ
#assert simplify(EG(TRUE())) == Not(AF(Not(TRUE())))# EGφ=¬AF¬φ
#assert simplify(rmimp(Not(Implies("x", "y")))) == Or("x", Not("y"))# Assertion Error


#Correctness checking --------------------------------------------------------------------------------------------------
#(((A & (B <=> C)) | ((D & -E) | (F & (G EU H))) & ((EX-(T AU I) & (AF-((J => K) & (L EU (AG M))) | ((EF N) & (AU (O | (EG P)) & (Q <=> -R))))))))
