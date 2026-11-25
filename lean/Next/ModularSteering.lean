import Next.ModularTrials
import Mathlib.Data.Int.ModEq

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- Integer versions of the three exact packet forms. -/
def intSeed (p y : ℤ) (i : Fin 3) : ℤ := slope i*y+intercept i*p

/-- The simultaneous divisibility requests reduce to one progression whose
modulus is no greater than the largest requested power of two. -/
theorem request_progression (p : ℤ) (e E : ℕ) (he : e≤E)
    (hp : (2:ℤ)^(e+1)∣p) (i : Fin 3) :
    ∃ m : ℕ, ∃ r : ℤ, 0<m ∧ m≤2^E ∧
      ∀ y : ℤ, (m:ℤ)∣y-r → (2:ℤ)^e∣y ∧ (2:ℤ)^E∣intSeed p y i := by
  have hpow : (2:ℤ)^e∣(2:ℤ)^E := pow_dvd_pow 2 he
  have hpp : (2:ℤ)^e∣p := (pow_dvd_pow 2 (by omega : e≤e+1)).trans hp
  by_cases h0 : i=0
  · refine ⟨2^E,0,by positivity,le_rfl,?_⟩
    intro y hy
    have hy' : (2:ℤ)^E∣y := by simpa using hy
    exact ⟨hpow.trans hy',by simpa [intSeed,slope,intercept,h0] using hy'⟩
  by_cases h1 : i=1
  · refine ⟨2^E,p,by positivity,le_rfl,?_⟩
    intro y hy
    have hy' : (2:ℤ)^E∣y-p := by simpa using hy
    have hl : (2:ℤ)^e∣y := by
      convert dvd_add (hpow.trans hy') hpp using 1 <;> ring
    refine ⟨hl,?_⟩
    have hn := dvd_neg.mpr hy'
    convert hn using 1 <;> simp [intSeed,slope,intercept,h1] <;> ring
  · obtain ⟨a,ha⟩ := hp
    let r : ℤ := (2:ℤ)^e*a
    have hpr : p=2*r := by rw [ha,pow_succ]; dsimp [r]; ring
    let f := max e (E-1)
    refine ⟨2^f,r,by positivity,Nat.pow_le_pow_right (by decide) (by dsimp [f]; omega),?_⟩
    intro y hy
    have hy' : (2:ℤ)^f∣y-r := by simpa using hy
    have hlow : (2:ℤ)^e∣y-r := (pow_dvd_pow 2 (le_max_left _ _)).trans hy'
    have hr : (2:ℤ)^e∣r := ⟨a,rfl⟩
    have hlo : (2:ℤ)^e∣y := by convert dvd_add hlow hr using 1 <;> ring
    refine ⟨hlo,?_⟩
    obtain ⟨b,hb⟩ := hy'
    have hd : (2:ℤ)^E∣(2:ℤ)^(f+1) := pow_dvd_pow 2 (by dsimp [f]; omega)
    apply hd.trans
    refine ⟨-b,?_⟩
    simp only [intSeed,slope,intercept,h0,h1,if_false]
    rw [hpr,pow_succ]
    nlinarith [hb]

/-- Integer signed trials in an arbitrary residue class avoid any small
finite forbidden set. Sign is selected to match the supplied input p. -/
theorem signed_trial (bad : Finset (ZMod q)) (F m W : ℕ) (p r : ℤ)
    (hF : bad.card≤F) (hm : 0<m) (hW : m*(F+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, 0 < |y| ∧ |y|≤W ∧ (0≤p → 0<y) ∧ (p<0 → y<0) ∧
      (m:ℤ)∣y-r ∧ (y:ZMod q)∉bad := by
  have hmZ : (0:ℤ)<m := by exact_mod_cast hm
  have get (r' : ℤ) (positive : Bool) : ∃ z : ℕ, 0<z ∧ z≤W ∧
      (z:ℤ) ≡ r' [ZMOD (m:ℤ)] ∧ signedResidue (q:=q) positive z∉bad := by
    let r0 := (r'%(m:ℤ)).toNat
    have hr0 : (r0:ℤ)=r'%(m:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hmZ))
    have hr : r0<m := by
      have hh := Int.emod_lt_of_pos r' hmZ
      exact_mod_cast (show (r0:ℤ)<m by rw [hr0]; exact hh)
    obtain ⟨z,hz,hzW,hmod,hbad⟩ := exists_small_reparameterized bad id Function.injective_id positive
      F m r0 W hF hm hr hW hWq
    have hmodZ : (z:ℤ)%(m:ℤ)=r'%(m:ℤ) := by
      rw [← hr0]
      exact_mod_cast hmod
    exact ⟨z,hz,hzW,hmodZ,hbad⟩
  by_cases hp : 0≤p
  · obtain ⟨z,hz,hzW,hmod,hbad⟩ := get r true
    refine ⟨z,by simpa using hz,by simpa using hzW,by intros; exact_mod_cast hz,by omega,?_,?_⟩
    · exact dvd_neg.mp (by simpa using (Int.modEq_iff_dvd.mp hmod))
    · simpa [signedResidue] using hbad
  · obtain ⟨z,hz,hzW,hmod,hbad⟩ := get (-r) false
    have hm' : -(z:ℤ) ≡ r [ZMOD (m:ℤ)] := by simpa using hmod.neg
    refine ⟨-(z:ℤ),by simpa using hz,by simpa using hzW,by omega,by intro _; exact neg_neg_of_pos (by exact_mod_cast hz),?_,?_⟩
    · exact dvd_neg.mp (by simpa using (Int.modEq_iff_dvd.mp hm'))
    · simpa [signedResidue] using hbad

/-- Forward steering for multiple requested outputs. The dominant output
gets exponent E, all outputs get exponent e, and every representative stays
within twice W. Only the input's prescribed divisibility is used. -/
theorem multiple_requests (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^(e+1)∣p) (hpW : |p|≤2*W) (i : Fin 3)
    (hW : 2^E*(2000*(S.card+3)+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤2*W) := by
  obtain ⟨m,r,hm,hmE,hr⟩ := request_progression p e E he hp i
  obtain ⟨y,hy0,hyW,hypos,hyneg,hym,hybad⟩ := signed_trial (forbidden S (p:ZMod q))
    (2000*(S.card+3)) m W p r (forbidden_card S (p:ZMod q)).le hm
    ((Nat.mul_le_mul_right _ hmE).trans hW) hWq
  have hyv := hr y hym
  have hpp : (2:ℤ)^e∣p := (pow_dvd_pow 2 (by omega : e≤e+1)).trans hp
  refine ⟨y,hybad,?_,hyv.2,?_⟩
  · intro j
    exact dvd_add (dvd_mul_of_dvd_right hyv.1 _) (dvd_mul_of_dvd_right hpp _)
  · intro j
    have hybounds := abs_le.mp hyW
    have hpbounds := abs_le.mp hpW
    have h20 : (2:Fin 3)≠0 := by decide
    have h21 : (2:Fin 3)≠1 := by decide
    by_cases hp0 : 0≤p
    · have hh := hypos hp0
      fin_cases j <;> norm_num [intSeed,slope,intercept] <;>
        apply abs_le.mpr <;> constructor <;> omega
    · have hh := hyneg (by omega)
      fin_cases j <;> norm_num [intSeed,slope,intercept] <;>
        apply abs_le.mpr <;> constructor <;> omega

theorem intSeed_cast (p y : ℤ) (i : Fin 3) :
    (intSeed p y i:ZMod q)=seed (p:ZMod q) (y:ZMod q) i := by
  simp [intSeed,seed]

/-- Parameter existence also covers root packets, without a regular input.
Only the actually used outputs are retained by the graph construction. -/
theorem exists_parameter (S : Finset (ZMod q)) (p : ZMod q)
    (hq : 2000*(S.card+3)≤q) : ∃ y : ZMod q, y∉forbidden S p := by
  classical
  have hc : (forbidden S p).card < (Finset.univ : Finset (ZMod q)).card := by
    simpa using (forbidden_card S p).trans_le hq
  have hn : ¬(Finset.univ : Finset (ZMod q)) ⊆ forbidden S p := by
    intro h
    have hh := Finset.card_le_card h
    omega
  obtain ⟨y,_,hy⟩ := Finset.not_subset.mp hn
  exact ⟨y,hy⟩

#print axioms multiple_requests
end FixedCore.ModularFamilies
