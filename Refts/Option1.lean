inductive Reft where
| unit
| int (n : Int)
| bool (b : Bool)
| add (r1 r2 : Reft)
| gt (r1 r2 : Reft)
| eq (r1 r2 : Reft)

inductive Val where
| unit
| int (n : Int)
| bool (b : Bool)
deriving DecidableEq

instance : Coe Int Val where
  coe := .int

instance : Coe Bool Val where
  coe := .bool

def toInt : Val → Option Int
| .int n => n
| _ => .none

notation:12 r1 " > " r2 => Reft.gt r1 r2
notation:12 r1 " == " r2 => Reft.eq r1 r2

def eval (r : Reft): Option Val := do
  match r with
  | .unit => return .unit
  | .int n => return n
  | .bool b => return b
  | .add r1 r2 => return (← toInt (← eval r1)) + (← toInt (← eval r2))
  | .gt r1 r2 => return .bool ((← toInt (← eval r1)) > (← toInt (← eval r2)))
  | .eq r1 r2 => return (← eval r1) == (← eval r2)

instance : OfNat Reft n where
  ofNat := .int n

instance : Add Reft where
  add := .add

inductive HasSort : Reft → Type → Type where
| int : HasSort (.int n) Int
| bool : HasSort (.bool b) Bool
| add : HasSort r1 Int → HasSort r2 Int → HasSort (r1 + r2) Int
| gt : HasSort r1 Int → HasSort r2 Int → HasSort (r1 > r2) Bool

mutual
inductive BaseTy where
| int : BaseTy
| bool : BaseTy
| arrow : Ty → Ty → BaseTy

inductive Ty where
| indexed : BaseTy → Reft → Ty
| constr : Ty → Reft → Ty
| exists : (Reft → Ty) → Ty
| forall : (Reft → Ty) → Ty
end

instance : Coe BaseTy Ty where
  coe b := .indexed b .unit

notation:12 t1 " ⇀ " t2 => BaseTy.arrow t1 t2
notation:12 b "[" r "]" => Ty.indexed b r
notation:12 "{" t " | " p "}" => Ty.constr t p
notation:12 "∃" v ": "  t => Ty.exists (fun v => t)
notation:12 "∀" v ": "  t => Ty.forall (fun v => t)

example : Ty := ∀x: {.int[x] | x > 0} ⇀ ∃v: {.int[v] | v == x + 1}

def sortOf : BaseTy → Type
| .int => Int
| .bool => Bool
| .arrow _ _ => Unit

mutual
inductive WfBty : BaseTy → Prop where
| int : WfBty .int
| bool : WfBty .bool
| arrow : WfTy t1 → WfTy t2 → WfBty (.arrow t1 t2)

inductive WfTy : Ty → Prop where
| indexed : HasSort r (sortOf b) → WfTy (.indexed b r)
| constr : HasSort r Bool → WfTy t → WfTy (.constr t r)
| exists : ∀ (r : Reft), WfTy (t r) → WfTy (.exists t)
| forall : ∀ (r : Reft), WfTy (t r) → WfTy (.forall t)
end

mutual
inductive SubBty : BaseTy → BaseTy → Prop where
| int : SubBty .int .int
| bool : SubBty .bool .bool
| arrow : SubTy t2 t1 → SubTy s1 s2 → SubBty (.arrow t1 s1) (.arrow t2 s2)

inductive SubTy : Ty → Ty → Prop where
| indexed : SubBty b1 b2 → eval r1 = eval r2 → SubTy (b1[r1]) (b2[r2])
| constr_l : eval r1 = .some (.bool b) → (b → SubTy t1 t2) → SubTy ({t1 | r1}) t2
| constr_r : eval r2 = true → SubTy t1 ({t2 | r2})
end

#check GetElem
