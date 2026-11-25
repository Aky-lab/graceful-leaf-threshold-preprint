import Next.ModularAvoidance

/-! Finite exclusions for the exact sibling/triple residue packets.
All estimates hold for composite moduli. -/
namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- No nonzero integer of absolute value at most sixteen annihilates z. -/
def Regular (z : ZMod q) : Prop := ∀ a : ℤ, a≠0 → a.natAbs≤16 → (a:ZMod q)*z≠0

def slope (i : Fin 3) : ℤ := if i=0 then 1 else if i=1 then -1 else -2
def intercept (i : Fin 3) : ℤ := if i=0 then 0 else 1
def seed (p y : ZMod q) (i : Fin 3) : ZMod q := (slope i:ZMod q)*y+(intercept i:ZMod q)*p

def sign (s : Bool) : ℤ := if s then 1 else -1

def dyad (t : Fin 3) : ℤ := 2^t.val

theorem slope_nonzero (i : Fin 3) : slope i≠0 := by fin_cases i <;> norm_num [slope]
theorem slope_abs (i : Fin 3) : (slope i).natAbs≤2 := by fin_cases i <;> norm_num [slope]
theorem dyad_pos (t : Fin 3) : 0<dyad t := by unfold dyad; positivity

abbrev SmallIndex := Fin 3 × Fin 16

def smallA (i : SmallIndex) : ℤ := (i.2.val+1)*slope i.1
def smallB (p : ZMod q) (i : SmallIndex) : ZMod q := -(((i.2.val+1:ℕ):ZMod q)*(intercept i.1:ZMod q)*p)

def smallBad (p : ZMod q) : Finset (ZMod q) :=
  Finset.univ.biUnion (fun i : SmallIndex => fiber (smallA i:ZMod q) (smallB p i))

theorem smallA_nonzero (i : SmallIndex) : smallA i≠0 := by
  exact mul_ne_zero (by omega) (slope_nonzero _)

theorem smallA_abs (i : SmallIndex) : (smallA i).natAbs≤32 := by
  rw [smallA,Int.natAbs_mul]
  have hs := slope_abs i.1
  have hi := i.2.isLt
  have he : ((i.2.val : ℤ)+1).natAbs=i.2.val+1 := by exact_mod_cast Int.natAbs_natCast (i.2.val+1)
  rw [he]
  nlinarith

theorem smallBad_card (p : ZMod q) : (smallBad p).card≤1536 := by
  calc
    _ ≤ ∑ i : SmallIndex,(smallA i).natAbs := card_affine_forbidden_le _ _ _ (fun i _ => smallA_nonzero i)
    _ ≤ ∑ _i : SmallIndex,32 := Finset.sum_le_sum (fun i _ => smallA_abs i)
    _ = 1536 := by norm_num [SmallIndex,Fintype.card_prod]

/-- Reserved dyadic classes of new seeds cannot meet those of old seeds. -/
abbrev OldIndex := Fin 3 × Fin 3 × Fin 3 × Bool × ZMod q

def oldA (i : OldIndex (q:=q)) : ℤ := dyad i.2.1*slope i.1
def oldB (p : ZMod q) (i : OldIndex (q:=q)) : ZMod q :=
  (sign i.2.2.2.1*dyad i.2.2.1:ℤ)*i.2.2.2.2-(dyad i.2.1*intercept i.1:ℤ)*p

def oldIndices (S : Finset (ZMod q)) : Finset (OldIndex (q:=q)) :=
  Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ S

def oldBad (S : Finset (ZMod q)) (p : ZMod q) : Finset (ZMod q) :=
  (oldIndices S).biUnion (fun i => fiber (oldA i:ZMod q) (oldB p i))

theorem oldA_nonzero (i : OldIndex (q:=q)) : oldA i≠0 :=
  mul_ne_zero (ne_of_gt (dyad_pos _)) (slope_nonzero _)

theorem oldA_abs (i : OldIndex (q:=q)) : (oldA i).natAbs≤8 := by
  rcases i with ⟨i,t,u,s,z⟩
  fin_cases i <;> fin_cases t <;> norm_num [oldA,dyad,slope]

theorem oldBad_card (S : Finset (ZMod q)) (p : ZMod q) : (oldBad S p).card≤432*S.card := by
  calc
    _ ≤ ∑ i∈oldIndices S,(oldA i).natAbs := card_affine_forbidden_le _ _ _ (fun i _ => oldA_nonzero i)
    _ ≤ ∑ _i∈oldIndices S,8 := Finset.sum_le_sum (fun i _ => oldA_abs i)
    _ = 432*S.card := by simp [oldIndices,Finset.card_product]; ring

abbrev InnerIndex := Fin 3 × Fin 3 × Fin 3 × Fin 3 × Bool

def innerA (i : InnerIndex) : ℤ := dyad i.2.2.1*slope i.1-sign i.2.2.2.2*dyad i.2.2.2.1*slope i.2.1
def innerC (i : InnerIndex) : ℤ := sign i.2.2.2.2*dyad i.2.2.2.1*intercept i.2.1-dyad i.2.2.1*intercept i.1

def innerIndices : Finset InnerIndex := Finset.univ.filter (fun i => i.1≠i.2.1 ∧ innerA i≠0)
def innerBad (p : ZMod q) : Finset (ZMod q) :=
  innerIndices.biUnion (fun i => fiber (innerA i:ZMod q) ((innerC i:ZMod q)*p))

theorem innerA_abs (i : InnerIndex) : (innerA i).natAbs≤16 := by
  rcases i with ⟨i,j,t,u,s⟩
  fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases u <;> cases s <;>
    norm_num [innerA,dyad,slope,sign]

theorem innerC_abs (i : InnerIndex) : (innerC i).natAbs≤8 := by
  rcases i with ⟨i,j,t,u,s⟩
  fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases u <;> cases s <;>
    norm_num [innerC,dyad,intercept,sign]

theorem innerC_nonzero (i : InnerIndex) (hi : i.1≠i.2.1) (ha : innerA i=0) : innerC i≠0 := by
  rcases i with ⟨i,j,t,u,s⟩
  fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases u <;> cases s <;>
    norm_num [innerA,innerC,dyad,slope,intercept,sign] at *

theorem innerBad_card (p : ZMod q) : (innerBad p).card≤2592 := by
  calc
    _ ≤ ∑ i∈innerIndices,(innerA i).natAbs := card_affine_forbidden_le _ _ _
      (fun i hi => (Finset.mem_filter.mp hi).2.2)
    _ ≤ ∑ _i∈innerIndices,16 := Finset.sum_le_sum (fun i _ => innerA_abs i)
    _ ≤ ∑ _i : InnerIndex,16 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ = 2592 := by norm_num [InnerIndex,Fintype.card_prod]

def forbidden (S : Finset (ZMod q)) (p : ZMod q) : Finset (ZMod q) := smallBad p ∪ oldBad S p ∪ innerBad p

theorem forbidden_card (S : Finset (ZMod q)) (p : ZMod q) :
    (forbidden S p).card < 2000*(S.card+3) := by
  have h := Finset.card_union_le (smallBad p ∪ oldBad S p) (innerBad p)
  have h' := Finset.card_union_le (smallBad p) (oldBad S p)
  have hs := smallBad_card p
  have ho := oldBad_card S p
  have hi := innerBad_card p
  dsimp [forbidden]
  omega

theorem regular_of_positive (z : ZMod q)
    (h : ∀ m : ℕ, 0<m → m≤16 → (m:ZMod q)*z≠0) : Regular z := by
  intro a ha hb
  cases a with
  | ofNat m =>
    have hm : m≠0 := by intro h; subst m; exact ha rfl
    simpa using h m (Nat.pos_of_ne_zero hm) hb
  | negSucc m =>
    have hh := h (m+1) (by omega) hb
    simpa only [Int.cast_negSucc,neg_mul,neg_ne_zero] using hh

theorem avoids_regular (S : Finset (ZMod q)) (p y : ZMod q)
    (hy : y∉forbidden S p) (i : Fin 3) : Regular (seed p y i) := by
  apply regular_of_positive
  intro m hm hm16 he
  let j : SmallIndex := (i,⟨m-1,by omega⟩)
  have hj : j.2.val+1=m := by dsimp [j]; omega
  have heq : (smallA j:ZMod q)*y=smallB p j := by
    dsimp [smallA,smallB]
    push_cast
    change ((j.2.val:ZMod q)+1)*(slope i:ZMod q)*y =
      -(((j.2.val:ZMod q)+1)*(intercept i:ZMod q)*p)
    have hj' : (j.2.val:ZMod q)+1=(m:ZMod q) := by simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun x : ℕ => (x:ZMod q)) hj
    rw [hj']
    dsimp [seed] at he
    linear_combination he
  apply hy
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq⟩⟩

/-- Disjointness of all signed tail classes through two halvings, expressed
without choosing inverse representatives. -/
def Separated (x y : ZMod q) : Prop := ∀ t u : Fin 3, ∀ e : Bool,
    (dyad t:ZMod q)*x≠((sign e*dyad u:ℤ):ZMod q)*y

theorem avoids_old (S : Finset (ZMod q)) (p y : ZMod q)
    (hy : y∉forbidden S p) (i : Fin 3) (z : ZMod q) (hz : z∈S) :
    Separated (seed p y i) z := by
  intro t u e he
  let j : OldIndex (q:=q) := (i,t,u,e,z)
  have hj : j∈oldIndices S := by simp [j,oldIndices,hz]
  have heq : (oldA j:ZMod q)*y=oldB p j := by
    dsimp [oldA,oldB,j,seed] at *
    push_cast at *
    linear_combination he
  apply hy
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq⟩⟩

theorem avoids_inner (S : Finset (ZMod q)) (p y : ZMod q) (hp : Regular p)
    (hy : y∉forbidden S p) (i j : Fin 3) (hij : i≠j) :
    Separated (seed p y i) (seed p y j) := by
  intro t u e he
  let v : InnerIndex := (i,j,t,u,e)
  have hv : v.1≠v.2.1 := hij
  have heq : (innerA v:ZMod q)*y=(innerC v:ZMod q)*p := by
    dsimp [innerA,innerC,v,seed] at *
    push_cast at *
    linear_combination he
  by_cases ha : innerA v=0
  · have hzero : (innerC v:ZMod q)*p=0 := by rw [ha,Int.cast_zero,zero_mul] at heq; exact heq.symm
    exact hp (innerC v) (innerC_nonzero v hv ha) ((innerC_abs v).trans (by decide)) hzero
  · apply hy
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,ha⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq⟩⟩

/-- The exact three-seed packet used along a singleton triple. Its signed
edge differences permute its seeds, independent of all avoidance choices. -/
theorem triple_differences (p y : ZMod q) :
    p-seed p y 0=seed p y 1 ∧
    seed p y 0-seed p y 1= -seed p y 2 ∧
    seed p y 1-seed p y 2=seed p y 0 := by
  have h20 : (2:Fin 3)≠0 := by decide
  have h21 : (2:Fin 3)≠1 := by decide
  norm_num [seed,slope,intercept,h20,h21]
  constructor <;> ring_nf <;> simp

/-- The first two seeds likewise match the sibling-edge differences. -/
theorem sibling_differences (p y : ZMod q) :
    p-seed p y 0=seed p y 1 ∧ p-seed p y 1=seed p y 0 := by
  norm_num [seed,slope,intercept]
  ring

/-- Unsteered packet existence over any sufficiently large modulus. -/
theorem exists_packet (S : Finset (ZMod q)) (p : ZMod q) (hp : Regular p)
    (hq : 2000*(S.card+3)≤q) :
    ∃ y : ZMod q, (∀ i,Regular (seed p y i)) ∧
      (∀ i z,z∈S → Separated (seed p y i) z) ∧
      (∀ i j,i≠j → Separated (seed p y i) (seed p y j)) := by
  classical
  have hc : (forbidden S p).card < (Finset.univ : Finset (ZMod q)).card := by
    simpa using (forbidden_card S p).trans_le hq
  have hn : ¬(Finset.univ : Finset (ZMod q)) ⊆ forbidden S p := by
    intro h
    have hh := Finset.card_le_card h
    omega
  obtain ⟨y,_,hy⟩ := Finset.not_subset.mp hn
  exact ⟨y,avoids_regular S p y hy,fun i z hz => avoids_old S p y hy i z hz,
    fun i j hij => avoids_inner S p y hp hy i j hij⟩

#print axioms exists_packet
end FixedCore.ModularFamilies
