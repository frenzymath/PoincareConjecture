import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Sphere








set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Topology ContinuousMap unitInterval

universe u

namespace Poincare.Topology


def puncturedSpaceSphereHomotopyEquiv
    (E : Type u) [NormedAddCommGroup E] [NormedSpace Real E] :
    {x : E | x ≠ 0} ≃ₕ sphere (0 : E) 1 := by
  let P := {x : E | x ≠ 0}
  have hn (x : P) : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
  have hq (x : P) : ‖x.val‖⁻¹ • x.val ∈ sphere (0 : E) 1 := by
    simp [norm_smul, hn x]
  let q : C(P, sphere (0 : E) 1) :=
    ⟨fun x => ⟨‖x.val‖⁻¹ • x.val, hq x⟩,
      ((continuous_subtype_val.norm.inv₀ hn).smul continuous_subtype_val).subtype_mk hq⟩
  let j : C(sphere (0 : E) 1, P) :=
    ⟨fun x => ⟨x.val, ne_zero_of_mem_sphere one_ne_zero x⟩,
      continuous_subtype_val.subtype_mk _⟩
  let c (z : unitInterval × P) : Real :=
    (1 - (z.1 : Real)) * ‖z.2.val‖⁻¹ + (z.1 : Real)
  have hcpos (z : unitInterval × P) : 0 < c z := by
    have hnorm : 0 < ‖z.2.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr z.2.property)
    by_cases ht : (z.1 : Real) = 1
    · simp [c, ht]
    · have hdiff : 0 < 1 - (z.1 : Real) :=
        sub_pos.mpr (lt_of_le_of_ne z.1.property.2 ht)
      exact add_pos_of_pos_of_nonneg (mul_pos hdiff hnorm) z.1.property.1
  have hc : Continuous c :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_subtype_val.comp continuous_snd).norm.inv₀ (fun z => hn z.2))).add
      (continuous_subtype_val.comp continuous_fst)
  let H : ContinuousMap.Homotopy (j.comp q) (ContinuousMap.id P) :=
    { toFun := fun z => ⟨c z • z.2.val, smul_ne_zero (hcpos z).ne' z.2.property⟩
      continuous_toFun := (hc.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left x := by
        apply Subtype.ext
        change c (0, x) • x.val = ‖x.val‖⁻¹ • x.val
        simp [c]
      map_one_left x := by
        apply Subtype.ext
        change c (1, x) • x.val = x.val
        simp [c] }
  refine ⟨q, j, ⟨H⟩, ?_⟩
  have hqj : q.comp j = ContinuousMap.id (sphere (0 : E) 1) := by
    ext x
    change ‖x.val‖⁻¹ • x.val = x.val
    simp [mem_sphere_zero_iff_norm.mp x.property]
  rw [hqj]


theorem exists_sphere_puncture_homeomorph
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] (n : Nat) [Fact (Module.finrank Real E = n + 1)]
    (v : sphere (0 : E) 1) :
    ∃ h : ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ EuclideanSpace Real (Fin n),
      h ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere Real v).symm⟩ = 0 := by
  let e := stereographic' n v
  let h : ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ EuclideanSpace Real (Fin n) :=
    (Homeomorph.setCongr (stereographic'_source v).symm).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))
  refine ⟨h, ?_⟩
  change stereographic' n v (-v) = 0
  simp [stereographic']


theorem exists_sphere_contractible_open_cover (n : Nat) :
    ∃ A B : Set (sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1),
      IsOpen A ∧ IsOpen B ∧ A ∪ B = Set.univ ∧
      ContractibleSpace A ∧ ContractibleSpace B ∧
      Nonempty (↥(A ∩ B) ≃ₕ sphere (0 : EuclideanSpace Real (Fin (n + 1))) 1) := by
  let E := EuclideanSpace Real (Fin (n + 2))
  let S := sphere (0 : E) 1
  let : Fact (Module.finrank Real E = (n + 1) + 1) := ⟨by simp [E]⟩
  have hSne : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨v, hv⟩ := hSne
  let p : S := ⟨v, hv⟩
  have hne : p ≠ -p := ne_neg_of_mem_unit_sphere Real p
  let A : Set S := {p}ᶜ
  let B : Set S := {-p}ᶜ
  obtain ⟨hA, hz⟩ := exists_sphere_puncture_homeomorph (n + 1) p
  obtain ⟨hB, _⟩ := exists_sphere_puncture_homeomorph (n + 1) (-p)
  have hcover : A ∪ B = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x = p
    · right
      simpa only [B, Set.mem_compl_iff, Set.mem_singleton_iff, hx] using hne
    · exact Or.inl hx
  let H : ↥(A ∩ B) ≃ₜ {x : A | x.val ≠ -p} :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hzero (x : A) : x.val ≠ -p ↔ hA x ≠ 0 := by
    rw [← hz, hA.injective.ne_iff]
    constructor
    · intro hx h
      exact hx (congrArg Subtype.val h)
    · intro hx h
      exact hx (Subtype.ext h)
  let G := hA.subtype (p := fun x : A => x.val ≠ -p)
    (q := fun x : EuclideanSpace Real (Fin (n + 1)) => x ≠ 0) hzero
  refine ⟨A, B, isOpen_compl_singleton, isOpen_compl_singleton, hcover,
    hA.contractibleSpace, hB.contractibleSpace, ?_⟩
  exact ⟨((H.trans G).toHomotopyEquiv).trans
    (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace Real (Fin (n + 1))))⟩

end Poincare.Topology
