import OAI.GroupTheory.ArtinCAT0.Eleven.Assembly

namespace OAI
namespace ArtinCAT0
namespace Eleven

open scoped Classical

/-! ## Group identities -/

section GroupIdentities
variable {G : Type*} [Group G]

/-- Garside element of a three-generator braid chain `p - q - r`. -/
lemma garside_conj {p q r : G} (hpq : p*q*p = q*p*q) (hqr : q*r*q = r*q*r) (hpr : p*r = r*p) :
    (p*q*p*r*q*p) * p * (p*q*p*r*q*p)⁻¹ = r ∧ (p*q*p*r*q*p) * q * (p*q*p*r*q*p)⁻¹ = q := by
  have h1 : (p*q*p*r*q*p) * p = r * (p*q*p*r*q*p) := by
    symm
    calc r * (p*q*p*r*q*p) = (r*p)*q*p*r*q*p := by group
      _ = (p*r)*q*p*r*q*p := congrArg (fun z => z*q*p*r*q*p) hpr.symm
      _ = p*r*q*(p*r)*q*p := by group
      _ = p*r*q*(r*p)*q*p := congrArg (fun z => p*r*q*z*q*p) hpr
      _ = p*(r*q*r)*p*q*p := by group
      _ = p*(q*r*q)*p*q*p := congrArg (fun z => p*z*p*q*p) hqr.symm
      _ = p*q*r*(q*p*q)*p := by group
      _ = p*q*r*(p*q*p)*p := congrArg (fun z => p*q*r*z*p) hpq.symm
      _ = p*q*(r*p)*q*p*p := by group
      _ = p*q*(p*r)*q*p*p := congrArg (fun z => p*q*z*q*p*p) hpr.symm
      _ = (p*q*p*r*q*p) * p := by group
  have h2 : (p*q*p*r*q*p) * q = q * (p*q*p*r*q*p) := by
    calc (p*q*p*r*q*p) * q = p*q*p*r*(q*p*q) := by group
      _ = p*q*p*r*(p*q*p) := congrArg (fun z => p*q*p*r*z) hpq.symm
      _ = p*q*p*(r*p)*q*p := by group
      _ = p*q*p*(p*r)*q*p := congrArg (fun z => p*q*p*z*q*p) hpr.symm
      _ = (p*q*p)*p*r*q*p := by group
      _ = (q*p*q)*p*r*q*p := congrArg (fun z => z*p*r*q*p) hpq
      _ = q * (p*q*p*r*q*p) := by group
  constructor
  · rw [h1]; group
  · rw [h2]; group

lemma cube_swap {u v : G} (h : u*v*u = v*u*v) : (u*v)^3 = (v*u)^3 := by
  calc (u*v)^3 = (u*v*u)*(v*u*v) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (v*u*v)*(u*v*u) := by rw [h]
    _ = (v*u)^3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

end GroupIdentities

/-! ## Ratios -/

section Ratios
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

noncomputable def R (x : X) (u v : G) : ℝ := stableLengthAt x ((u*v)^3) / (3 * stableLengthAt x (u^2))

lemma R_conj (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) (g u v : G) :
    R x (g*u*g⁻¹) (g*v*g⁻¹) = R x u v := by
  unfold R
  have h1 : (g*u*g⁻¹ * (g*v*g⁻¹))^3 = g * (u*v)^3 * g⁻¹ := by
    rw [show g*u*g⁻¹ * (g*v*g⁻¹) = g*(u*v)*g⁻¹ by group, conj_pow]
  have h2 : (g*u*g⁻¹)^2 = g * u^2 * g⁻¹ := conj_pow
  rw [h1, h2, stableLength_conjugate hi, stableLength_conjugate hi]

lemma R_swap (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) {u v : G}
    (h : u*v*u = v*u*v) : R x u v = R x v u := by
  unfold R
  rw [cube_swap h]
  have hc : (u*v)*u*(u*v)⁻¹ = v := braid_conjugate h
  have : stableLengthAt x (v^2) = stableLengthAt x (u^2) := by
    rw [← hc]
    have : ((u*v)*u*(u*v)⁻¹)^2 = (u*v) * u^2 * (u*v)⁻¹ := conj_pow
    rw [this, stableLength_conjugate hi]
  rw [this]

end Ratios

/-! ## The braid chain `a, b, x1, ..., x7` -/

def chainLetter (n : Fin 9) : Fin 11 :=
  if n.val < 2 then ⟨n.val, by omega⟩ else ⟨n.val + 2, by omega⟩

lemma chain_adj : ∀ i j : Fin 9, i.val + 1 = j.val → lab (chainLetter i) (chainLetter j) = 3 := by
  decide
lemma chain_far : ∀ i j : Fin 9, i.val + 2 ≤ j.val → lab (chainLetter i) (chainLetter j) = 2 := by
  decide

def chainMain : BraidGroup 9 →* MainGroup := braidLift (fun n => mainGen (chainLetter n))
  (fun i hi => main_braid _ _ (chain_adj ⟨i, by omega⟩ ⟨i+1, hi⟩ rfl))
  (fun i j hij => main_commute _ _ (chain_far i j hij))

def chainS (n : ℕ) : MainGroup := chainMain (braidGen 9 n)

lemma chainS_lt (n : ℕ) (hn : n < 9) : chainS n = mainGen (chainLetter ⟨n, hn⟩) := by
  simp [chainS, braidGen, hn, chainMain]

lemma chain_relations : BraidRelations 9 chainS := by
  constructor
  · intro j hj
    simpa only [chainS, map_mul] using congrArg chainMain ((braidGroup_relations 9).1 j hj)
  · intro j k hj hk hjk
    exact ((braidGroup_relations 9).2 j k hj hk hjk).map chainMain

/-! ## The full twist has infinite order -/

section Exponent
variable {K : Type*} [CommGroup K]

lemma braidLoop_const (g : K) (n : ℕ) : braidLoop (fun _ => g) n = g^(2*n) := by
  induction n with
  | zero => simp [braidLoop]
  | succ n ih =>
    simp only [braidLoop, ih]
    rw [show 2*(n+1) = 1 + 2*n + 1 by ring, pow_add, pow_add, pow_one]

lemma braidCenter_const (g : K) (n : ℕ) : braidCenter (fun _ => g) n = g^(n*(n+1)) := by
  induction n with
  | zero => simp [braidCenter]
  | succ n ih =>
    simp only [braidCenter, ih, braidLoop_const, ← pow_add]
    congr 1
    ring

end Exponent

lemma twist_infinite_order : ¬ IsOfFinOrder (braidCenter chainS 9) := by
  intro hf
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hh := congrArg (artinExponent M11) he
  rw [map_pow, map_one, map_braidCenter] at hh
  have hc : braidCenter (fun i => artinExponent M11 (chainS i)) 9 =
      braidCenter (fun _ => Multiplicative.ofAdd (1:ℤ)) 9 := by
    apply braidCenter_congr
    intro i hi
    rw [chainS_lt i hi, artinExponent_of]
  rw [hc, braidCenter_const, ← pow_mul] at hh
  have hz := congrArg Multiplicative.toAdd hh
  simp at hz
  omega

/-! ## Main theorem -/

def tuple (i : Bool) : MainGroup := if i then mainGen 6 else mainGen 3

lemma triMain_tuple (t : TriangleGroup) : ∀ i, Commute (triMain t) (tuple i) := by
  intro i; cases i
  · exact triMain_commute_e t
  · exact triMain_commute_x3 t

def triangleCentralizer : TriangleGroup →* tupleCentralizer tuple :=
  triMain.codRestrict _ triMain_tuple

lemma triangleCentralizer_bijective (hT : Function.Injective t0) :
    Function.Bijective triangleCentralizer := by
  constructor
  · intro a b h
    exact triMain_injective hT (congrArg Subtype.val h)
  · intro g
    obtain ⟨t, ht⟩ := common_centralizer hT g.val (g.property false) (g.property true)
    exact ⟨t, Subtype.ext ht⟩

universe u

/-- Ratios for the three triangle pairs in any geometric action of the 11-generator group. -/
lemma pair_ratios {X : Type u} [MetricSpace X] [ProperSpace X] [Nonempty X] [MulAction MainGroup X]
    (hG : GeometricAction MainGroup X) (x : X) :
    1/2 < R x (mainGen 0) (mainGen 1) ∧ 1/2 < R x (mainGen 1) (mainGen 2) ∧
      1/2 < R x (mainGen 2) (mainGen 0) := by
  have hi := hG.2.1
  have hs := chain_relations
  have hD : 0 < stableLengthAt x ((chainS 0)^2) := by
    rw [chainS_lt 0 (by norm_num)]
    exact generator_square_positive M11 hG x _
  have hZ : 0 < stableLengthAt x (braidCenter chainS 9) := by
    apply lt_of_le_of_ne (stableLength_nonneg hi x _)
    intro h
    exact twist_infinite_order ((stableLength_eq_zero_iff_finiteOrder hG x _).mp h.symm)
  have h01 : 1/2 < R x (chainS 0) (chainS 1) := (braid_ten_ratio hG x hs hD hZ).1
  have hs0 : chainS 0 = mainGen 0 := chainS_lt 0 (by norm_num)
  have hs1 : chainS 1 = mainGen 1 := chainS_lt 1 (by norm_num)
  have hs2 : chainS 2 = mainGen 4 := chainS_lt 2 (by norm_num)
  have hs3 : chainS 3 = mainGen 5 := chainS_lt 3 (by norm_num)
  -- (x1, x2) is a shift of (a, b)
  have h23 : R x (mainGen 4) (mainGen 5) = R x (mainGen 0) (mainGen 1) := by
    have c0 := braidDelta_pow_conjugate hs (i := 0) (k := 2) (by norm_num)
    have c1 := braidDelta_pow_conjugate hs (i := 1) (k := 2) (by norm_num)
    simp only [Nat.zero_add] at c0
    have c1' : (braidDelta chainS 9)^2 * chainS 1 * ((braidDelta chainS 9)^2)⁻¹ = chainS 3 := c1
    have := R_conj hi x ((braidDelta chainS 9)^2) (chainS 0) (chainS 1)
    rw [c0, c1', hs0, hs1, hs2, hs3] at this
    exact this
  -- (x1, x2) ~ (c, x2) ~ (c, a) and (c, b)
  have hcx : R x (mainGen 2) (mainGen 5) = R x (mainGen 4) (mainGen 5) := by
    obtain ⟨hp, hq⟩ := garside_conj (main_braid 4 5 (by decide)) (main_braid 5 2 (by decide))
      (main_commute 4 2 (by decide)).eq
    have := R_conj hi x (mainGen 4 * mainGen 5 * mainGen 4 * mainGen 2 * mainGen 5 * mainGen 4)
      (mainGen 4) (mainGen 5)
    rw [hp, hq] at this
    exact this
  have hca : R x (mainGen 2) (mainGen 0) = R x (mainGen 2) (mainGen 5) := by
    obtain ⟨hp, hq⟩ := garside_conj (main_braid 5 2 (by decide)) (main_braid 2 0 (by decide))
      (main_commute 5 0 (by decide)).eq
    have := R_conj hi x (mainGen 5 * mainGen 2 * mainGen 5 * mainGen 0 * mainGen 2 * mainGen 5)
      (mainGen 2) (mainGen 5)
    rw [hq, hp] at this
    exact this
  have hcb : R x (mainGen 2) (mainGen 1) = R x (mainGen 2) (mainGen 5) := by
    obtain ⟨hp, hq⟩ := garside_conj (main_braid 5 2 (by decide)) (main_braid 2 1 (by decide))
      (main_commute 5 1 (by decide)).eq
    have := R_conj hi x (mainGen 5 * mainGen 2 * mainGen 5 * mainGen 1 * mainGen 2 * mainGen 5)
      (mainGen 2) (mainGen 5)
    rw [hq, hp] at this
    exact this
  have hbase : 1/2 < R x (mainGen 0) (mainGen 1) := by rwa [hs0, hs1] at h01
  refine ⟨hbase, ?_, ?_⟩
  · rw [R_swap hi x (main_braid 1 2 (by decide)), hcb, hcx, h23]
    exact hbase
  · rw [hca, hcx, h23]
    exact hbase

theorem not_geometric (hT : Function.Injective t0) (X : Type u) [MetricSpace X] [ProperSpace X]
    [Nonempty X] [MulAction MainGroup X] : ¬GeometricAction MainGroup X := by
  classical
  intro hG
  obtain ⟨A, hA, hY⟩ := exists_sublevel_nonempty (X := X) tuple
  let Y := displacementSublevel (X := X) tuple A
  let : Nonempty Y := hY
  let : ProperSpace Y := sublevel_properSpace hG.2.1 tuple A
  let := sublevelAction hG.2.1 tuple A
  have hC := geometric_tupleCentralizer hG tuple A hA
  let := MulAction.compHom Y triangleCentralizer
  have hTY : GeometricAction TriangleGroup Y :=
    geometric_compHom triangleCentralizer (triangleCentralizer_bijective hT) hC
  let y : Y := Classical.choice inferInstance
  have hl (g : TriangleGroup) : stableLengthAt y g = stableLengthAt y.val (triMain g) := by
    rw [stableLength_compHom triangleCentralizer]
    exact sublevelAction_stableLength hG.2.1 tuple A y (triangleCentralizer g)
  obtain ⟨r0, r1, r2⟩ := pair_ratios hG y.val
  apply SixSector.no_strict_ratios hTY y
  intro i
  rw [hl, hl, triangleH, map_pow, map_pow, map_mul, triMain_gen, triMain_gen]
  fin_cases i
  · exact r0
  · exact r1
  · exact r2

/-- **Main theorem.**  Assuming the triangle group embeds in the Artin group `G0` on the
ten non-sentinel letters (a special case of van der Lek's theorem), the 11-generator Artin
group `A(M11)` admits no geometric action on a CAT(0) space. -/
theorem main (hT : Function.Injective t0) :
    (∀ s t : Fin 11, M11 s t = M11 t s) ∧
    (∀ s : Fin 11, M11 s s = 1) ∧
    (∀ s t : Fin 11, s ≠ t → M11 s t = 2 ∨ M11 s t = 3 ∨ M11 s t = ⊤) ∧
    (∀ (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
      [MulAction (ArtinGroup M11) X], ¬ GeometricAction (ArtinGroup M11) X) :=
  ⟨M11_symmetric, M11_diagonal, M11_values, fun X _ _ _ _ => not_geometric hT X⟩

end Eleven
end ArtinCAT0
end OAI
