import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Exhaustion

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.OpenCylinderModel

abbrev domain : Opens RoundCylinderSpace :=
  ⟨univ ×ˢ Ioo (0 : ℝ) 1, isOpen_univ.prod isOpen_Ioo⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

noncomputable def ofDiffeomorph (U : Opens M)
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) domain U ∞)
    (q₀ : UnitTwoSphere) : OpenCylinderModel (U : Set M) := by
  classical
  let z₀ : domain := ⟨(q₀, 1 / 2), mem_univ _, by norm_num⟩
  let f : RoundCylinderSpace → M :=
    Subtype.val.extend (fun z : domain => (e z : M)) (fun _ => (e z₀ : M))
  let g : M → RoundCylinderSpace :=
    Subtype.val.extend (fun x : U => (e.symm x : RoundCylinderSpace)) (fun _ => z₀)
  have hf (z : domain) : f z = (e z : M) := Subtype.val_injective.extend_apply _ _ z
  have hg (x : U) : g x = (e.symm x : RoundCylinderSpace) :=
    Subtype.val_injective.extend_apply _ _ x
  let h : (UnitTwoSphere × Ioo (0 : ℝ) 1) ≃ₜ domain :=
    (((Homeomorph.Set.univ UnitTwoSphere).symm).prodCongr
      (Homeomorph.refl (Ioo (0 : ℝ) 1))).trans
      (Homeomorph.Set.prod (univ : Set UnitTwoSphere) (Ioo (0 : ℝ) 1)).symm
  refine { homeomorph := h.trans e.toHomeomorph
           coordinate := f
           coordinate_eq := fun z => (hf (h z)).symm
           coordinate_smooth := ?_
           inverse := g
           inverse_mem := ?_
           left_inverse := ?_
           right_inverse := ?_
           inverse_smooth := ?_ }
  · intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff (x := (⟨z, hz⟩ : domain))).mp
    have heq : (fun w : domain => f w) = (fun w => (e w : M)) := funext hf
    rw [heq]
    exact (contMDiff_subtype_val.comp e.contMDiff).contMDiffAt
  · intro x hx
    rw [hg ⟨x, hx⟩]
    exact (e.symm ⟨x, hx⟩).property
  · intro z hz
    rw [hf ⟨z, hz⟩, hg (e ⟨z, hz⟩)]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  · intro x hx
    rw [hg ⟨x, hx⟩, hf (e.symm ⟨x, hx⟩)]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
    have heq : (fun y : U => g y) = (fun y => (e.symm y : RoundCylinderSpace)) :=
      funext hg
    rw [heq]
    exact (contMDiff_subtype_val.comp e.symm.contMDiff).contMDiffAt

@[simp] theorem ofDiffeomorph_coordinate (U : Opens M)
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) domain U ∞)
    (q₀ : UnitTwoSphere) (z : domain) :
    (ofDiffeomorph U e q₀).coordinate z = e z := by
  simp only [ofDiffeomorph, Subtype.val_injective.extend_apply]

@[simp] theorem ofDiffeomorph_inverse (U : Opens M)
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) domain U ∞)
    (q₀ : UnitTwoSphere) (x : U) :
    (ofDiffeomorph U e q₀).inverse x = e.symm x := by
  simp only [ofDiffeomorph, Subtype.val_injective.extend_apply]

theorem ofDiffeomorph_middleSphere (U : Opens M)
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) domain U ∞)
    (q₀ : UnitTwoSphere) :
    (ofDiffeomorph U e q₀).middleSphere =
      range (fun q : UnitTwoSphere => (e ⟨(q, 1 / 2), mem_univ _, by norm_num⟩ : M)) := by
  ext x
  constructor
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, h⟩
    have ht' : t = 1 / 2 := ht
    subst t
    exact ⟨q, (ofDiffeomorph_coordinate U e q₀
      ⟨(q, 1 / 2), mem_univ _, by norm_num⟩).symm.trans h⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩,
      ofDiffeomorph_coordinate U e q₀ ⟨(q, 1 / 2), mem_univ _, by norm_num⟩⟩

theorem exists_of_monotone_open_cover
    (A : ℕ → Opens domain) (V : ℕ → Opens M)
    (e : ∀ n, Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (A n) (V n) ∞)
    (hmono : Monotone A) (hcover : ∀ z, ∃ n, z ∈ A n)
    (hagree : ∀ (n m : ℕ) (x : A n) (y : A m),
      (x : domain) = y → (e n x : M) = e m y) (q₀ : UnitTwoSphere) :
    ∃ T : OpenCylinderModel ((⨆ n, V n : Opens M) : Set M),
      (∀ (n : ℕ) (z : A n), T.coordinate z.1.1 = e n z) ∧
      (∀ (n : ℕ) (x : V n), T.inverse x = ((e n).symm x).1.1) := by
  obtain ⟨F, hF, hFinv, -⟩ :=
    Poincare.exists_diffeomorph_of_monotone_open_cover A V e hmono hcover hagree
  refine ⟨ofDiffeomorph (⨆ n, V n) F q₀, ?_, ?_⟩
  · intro n z
    exact (ofDiffeomorph_coordinate _ F q₀ z.1).trans (hF n z)
  · intro n x
    rw [ofDiffeomorph_inverse _ F q₀
      ⟨x, Opens.mem_iSup.mpr ⟨n, x.property⟩⟩]
    exact congrArg Subtype.val (hFinv n x)

end PoincareConjecture.OpenCylinderModel
