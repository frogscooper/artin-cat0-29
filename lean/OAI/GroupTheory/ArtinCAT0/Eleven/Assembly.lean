import OAI.GroupTheory.ArtinCAT0.Eleven.Basic

/-!
# The 11-generator group as an amalgam, and its common centralizer

`G = G0 *_T (T × ⟨e⟩)`.  The amalgam normal form needs the triangle group to embed
in `G0` (a special case of van der Lek's theorem on standard parabolic subgroups);
this is the hypothesis `hT` below.  Everything else is proved.
-/

namespace OAI
namespace ArtinCAT0
namespace Eleven

open BinaryAmalgam
open scoped Classical

abbrev Cyc := Multiplicative ℤ
def E : Cyc := Multiplicative.ofAdd 1
lemma E_ne_one : E ≠ 1 := by
  intro h
  exact Int.one_ne_zero (Multiplicative.ofAdd.injective h)

abbrev Prod' := TriangleGroup × Cyc
def pT : TriangleGroup →* Prod' := (MonoidHom.id _).prod 1
lemma pT_injective : Function.Injective pT := fun a b h => congrArg Prod.fst h

abbrev Model := GroupOf t0 pT
def sentinel : Model := right t0 pT (1, E)

/-- Inverse of `ι` away from the sentinel letter `3` (junk value at `3`). -/
def jInv (s : Fin 11) : Fin 10 :=
  if h : s.val < 3 then ⟨s.val, by omega⟩ else if s.val = 3 then 0
  else ⟨s.val - 1, by have := s.isLt; omega⟩

lemma ι_jInv : ∀ s : Fin 11, s.val ≠ 3 → ι (jInv s) = s := by decide

def letter (s : Fin 11) : Model := if s.val = 3 then sentinel else left t0 pT (g0Gen (jInv s))

lemma letter_of_ne {s : Fin 11} (h : s.val ≠ 3) : letter s = left t0 pT (g0Gen (jInv s)) := by
  simp [letter, h]

lemma letter_three : letter 3 = sentinel := by simp [letter]

lemma lab_three_two : ∀ t : Fin 11, lab 3 t = 2 → t.val < 3 := by decide
lemma lab_three_three : ∀ t : Fin 11, lab 3 t ≠ 3 := by decide
lemma lab_jInv : ∀ s t : Fin 11, s.val ≠ 3 → t.val ≠ 3 → lab (ι (jInv s)) (ι (jInv t)) = lab s t := by
  intro s t hs ht; rw [ι_jInv s hs, ι_jInv t ht]

/-- The triangle generators of `G0`, seen in the model, lie in the `T × ⟨e⟩` factor. -/
lemma left_corner (k : Fin 3) :
    left t0 pT (g0Gen ⟨k.val, by omega⟩) = right t0 pT (triangleGen k, 1) := by
  have h := DFunLike.congr_fun (agree t0 pT) (triangleGen k)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, t0_gen] at h
  simpa [pT] using h

lemma sentinel_commute_corner (t : Fin 11) (ht : t.val < 3) : Commute sentinel (letter t) := by
  rw [letter_of_ne (by omega)]
  have hj : jInv t = ⟨t.val, by omega⟩ := by
    unfold jInv; simp [ht]
  rw [hj, left_corner ⟨t.val, ht⟩, sentinel]
  apply Commute.map
  apply Prod.ext <;> simp [mul_comm]

def toModel : MainGroup →* Model := artinLift M11 letter (by
  intro s t n hn
  rcases M11_cases hn with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    by_cases hs : s.val = 3
    · have : s = 3 := Fin.ext hs
      subst this
      rw [letter_three]
      exact sentinel_commute_corner t (lab_three_two t h)
    by_cases ht : t.val = 3
    · have : t = 3 := Fin.ext ht
      subst this
      rw [letter_three]
      exact (sentinel_commute_corner s (lab_three_two s (by rw [lab_symm]; exact h))).symm
    rw [letter_of_ne hs, letter_of_ne ht]
    exact (g0_commute _ _ (by rw [lab_jInv s t hs ht]; exact h)).map _
  · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    have hs : s.val ≠ 3 := by
      intro hs; have : s = 3 := Fin.ext hs; subst this; exact lab_three_three t h
    have ht : t.val ≠ 3 := by
      intro ht; have : t = 3 := Fin.ext ht; subst this
      exact lab_three_three s (by rw [lab_symm]; exact h)
    rw [letter_of_ne hs, letter_of_ne ht]
    simpa only [map_mul] using congrArg (left t0 pT) (g0_braid _ _ (by rw [lab_jInv s t hs ht]; exact h)))

@[simp] lemma toModel_gen (s : Fin 11) : toModel (mainGen s) = letter s := artinLift_of _ _ _ _

/-! ## The map back -/

def g0Main : G0 →* MainGroup := artinLift M0 (fun i => mainGen (ι i)) (by
  intro s t n hn
  rcases M11_cases hn with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl (ι_injective h)
  · exact Or.inr (Or.inl ⟨rfl, main_commute _ _ h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, main_braid _ _ h⟩)))

@[simp] lemma g0Main_gen (i : Fin 10) : g0Main (g0Gen i) = mainGen (ι i) := artinLift_of _ _ _ _

def triMain : TriangleGroup →* MainGroup := triangleLift (fun k => mainGen ⟨k.val, by omega⟩) (by
  intro k
  apply main_braid
  fin_cases k <;> decide)

@[simp] lemma triMain_gen (k : Fin 3) : triMain (triangleGen k) = mainGen ⟨k.val, by omega⟩ :=
  triangleLift_gen _ _ _

lemma triMain_commute_gen (t : TriangleGroup) (s : Fin 11)
    (hs : ∀ k : Fin 3, lab ⟨k.val, by omega⟩ s = 2) : Commute (triMain t) (mainGen s) := by
  let C := (Subgroup.centralizer {mainGen s}).comap triMain
  have hgen (k : Fin 3) : PresentedGroup.of (rels := triangleRelators) k ∈ C := by
    change triMain (triangleGen k) ∈ Subgroup.centralizer {mainGen s}
    rw [triMain_gen, Subgroup.mem_centralizer_singleton_iff]
    exact (main_commute _ _ (hs k)).eq
  have := PresentedGroup.generated_by triangleRelators C hgen t
  exact Subgroup.mem_centralizer_singleton_iff.mp this

lemma triMain_commute_e (t : TriangleGroup) : Commute (triMain t) (mainGen 3) :=
  triMain_commute_gen t 3 (by decide)

lemma triMain_commute_x3 (t : TriangleGroup) : Commute (triMain t) (mainGen 6) :=
  triMain_commute_gen t 6 (by decide)

def prodMain : Prod' →* MainGroup :=
  triMain.noncommCoprod (zpowersHom MainGroup (mainGen 3)) (by
    intro t z
    simpa [zpowersHom_apply] using (triMain_commute_e t).zpow_right z.toAdd)

@[simp] lemma prodMain_apply (t : TriangleGroup) (z : Cyc) :
    prodMain (t, z) = triMain t * (mainGen 3) ^ z.toAdd := by
  simp [prodMain, zpowersHom_apply]

lemma agree_back : g0Main.comp t0 = prodMain.comp pT := by
  apply PresentedGroup.ext
  intro k
  change g0Main (t0 (triangleGen k)) = prodMain (pT (triangleGen k))
  rw [t0_gen, g0Main_gen]
  simp only [pT, MonoidHom.prod_apply, MonoidHom.id_apply, MonoidHom.one_apply, prodMain_apply,
    triMain_gen, toAdd_one, zpow_zero, mul_one]
  congr 1
  fin_cases k <;> rfl

def fromModel : Model →* MainGroup := lift g0Main prodMain agree_back

lemma fromModel_letter : ∀ s : Fin 11, fromModel (letter s) = mainGen s := by
  intro s
  by_cases hs : s.val = 3
  · have : s = 3 := Fin.ext hs
    subst this
    rw [letter_three, sentinel, fromModel, lift_right, prodMain_apply]
    simp [E]
  · rw [letter_of_ne hs, fromModel, lift_left, g0Main_gen, ι_jInv s hs]

lemma fromModel_toModel : fromModel.comp toModel = MonoidHom.id MainGroup := by
  apply PresentedGroup.ext
  intro s
  change fromModel (toModel (mainGen s)) = mainGen s
  rw [toModel_gen, fromModel_letter]

lemma toModel_injective : Function.Injective toModel := by
  intro a b h
  have := congrArg fromModel h
  simpa [← MonoidHom.comp_apply, fromModel_toModel] using this

lemma toModel_triMain : toModel.comp triMain = (left t0 pT).comp t0 := by
  apply PresentedGroup.ext
  intro k
  change toModel (triMain (triangleGen k)) = left t0 pT (t0 (triangleGen k))
  rw [triMain_gen, toModel_gen, t0_gen, letter_of_ne (by simp; omega)]
  congr 2
  fin_cases k <;> rfl

lemma t0_commute_x3 (t : TriangleGroup) : Commute (t0 t) (g0Gen 5) := by
  let C := (Subgroup.centralizer {g0Gen 5}).comap t0
  have hgen (k : Fin 3) : PresentedGroup.of (rels := triangleRelators) k ∈ C := by
    change t0 (triangleGen k) ∈ Subgroup.centralizer {g0Gen 5}
    rw [t0_gen, Subgroup.mem_centralizer_singleton_iff]
    exact (g0_commute _ _ (by fin_cases k <;> decide)).eq
  have := PresentedGroup.generated_by triangleRelators C hgen t
  exact Subgroup.mem_centralizer_singleton_iff.mp this

lemma prod_conj_not_base (z : Cyc) (hz : z ≠ 1) (b : Prod') : b * (1, z) * b⁻¹ ∉ pT.range := by
  rintro ⟨a, ha⟩
  have h2 := congrArg Prod.snd ha
  simp [pT] at h2
  exact hz (by simpa [mul_comm] using h2.symm)

/-! ## Results under the van der Lek hypothesis -/

section WithEmbedding

variable (hT : Function.Injective t0)
include hT

lemma triMain_injective : Function.Injective triMain := by
  intro a b h
  have h' := congrArg toModel h
  change (toModel.comp triMain) a = (toModel.comp triMain) b at h'
  rw [toModel_triMain] at h'
  exact hT (left_injective hT pT_injective h')

theorem common_centralizer (g : MainGroup) (he : Commute g (mainGen 3))
    (hx : Commute g (mainGen 6)) : g ∈ triMain.range := by
  have he' : Commute (toModel g) sentinel := by
    simpa [letter_three] using he.map toModel
  have hx' : Commute (toModel g) (left t0 pT (g0Gen 5)) := by
    have := hx.map toModel
    rwa [toModel_gen, letter_of_ne (by decide)] at this
  obtain ⟨b, hb⟩ := centralizer_right hT pT_injective (1, E) (prod_conj_not_base E E_ne_one)
    (toModel g) he'
  obtain ⟨t, z⟩ := b
  -- the cyclic part commutes with x3
  have hsplit : right t0 pT (t, z) = left t0 pT (t0 t) * right t0 pT (1, z) := by
    have h := DFunLike.congr_fun (agree t0 pT) t
    simp only [MonoidHom.comp_apply] at h
    rw [h, ← map_mul]
    simp [pT]
  have hz : Commute (right t0 pT (1, z)) (left t0 pT (g0Gen 5)) := by
    have h1 : Commute (right t0 pT (t, z)) (left t0 pT (g0Gen 5)) := hb ▸ hx'
    rw [hsplit] at h1
    have h2 : Commute (left t0 pT (t0 t)) (left t0 pT (g0Gen 5)) := (t0_commute_x3 t).map _
    have h3 := h2.inv_left.mul_left h1
    simpa [← mul_assoc] using h3
  have hz1 : z = 1 := by
    by_contra hne
    have hmem := centralizer_right hT pT_injective (1, z) (prod_conj_not_base z hne)
      (left t0 pT (g0Gen 5)) hz.symm
    have hboth : left t0 pT (g0Gen 5) ∈
        (Monoid.PushoutI.of (φ := diagram t0 pT) false).range ⊓
          (Monoid.PushoutI.of (φ := diagram t0 pT) true).range := ⟨⟨_, rfl⟩, hmem⟩
    rw [Monoid.PushoutI.inf_of_range_eq_base_range (diagram_injective hT pT_injective)
      Bool.false_ne_true] at hboth
    obtain ⟨h, hh⟩ := hboth
    have hh' : left t0 pT (t0 h) = left t0 pT (g0Gen 5) := by
      rw [← hh]
      exact (Monoid.PushoutI.of_apply_eq_base (diagram t0 pT) false h)
    exact x3_not_in_triangle ⟨h, left_injective hT pT_injective hh'⟩
  subst hz1
  refine ⟨t, toModel_injective ?_⟩
  change (toModel.comp triMain) t = toModel g
  rw [toModel_triMain, ← hb]
  exact DFunLike.congr_fun (agree t0 pT) t

end WithEmbedding

end Eleven
end ArtinCAT0
end OAI
