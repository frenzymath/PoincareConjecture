import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.LocalConstruction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_disjoint_planar_translation {S T : Set P2}
    (hS : IsCompact S) (hT : IsCompact T) :
    ∃ a : P2 ≃ᴬ[ℝ] P2, Disjoint S (a '' T) := by
  obtain ⟨r,hr,hbound⟩ := (hS.union hT).isBounded.exists_pos_norm_le
  let a := ContinuousAffineEquiv.constVAdd ℝ P2 (3 * r, 0)
  refine ⟨a,disjoint_left.mpr ?_⟩
  rintro z hz ⟨w,hw,rfl⟩
  have hzbound := hbound _ (Or.inl hz)
  have hwbound := hbound _ (Or.inr hw)
  have hzfst : |(a w).1| ≤ r :=
    (show ‖(a w).1‖ ≤ ‖a w‖ from norm_fst_le _).trans hzbound
  have hwfst : |w.1| ≤ r := (norm_fst_le w).trans hwbound
  change |3 * r + w.1| ≤ r at hzfst
  have := (abs_le.mp hzfst).2
  have := (abs_le.mp hwfst).1
  linarith

theorem exists_disjoint_planar_source_map
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K₀ K₁ : SimplicialComplex ℝ P2) (hK₀ : K₀.faces.Finite) (hK₁ : K₁.faces.Finite)
    (f₀ f₁ : P2 → X) (hf₀ : PolyhedralPLInCharts e f₀ K₀.space)
    (hf₁ : PolyhedralPLInCharts e f₁ K₁.space) :
    ∃ (a : P2 ≃ᴬ[ℝ] P2) (L : SimplicialComplex ℝ P2) (f : P2 → X),
      Disjoint K₀.space (a '' K₁.space) ∧ L.faces.Finite ∧
      L.space = K₀.space ∪ a '' K₁.space ∧ PolyhedralPLInCharts e f L.space ∧
      EqOn f f₀ K₀.space ∧ (∀ x ∈ K₁.space, f (a x) = f₁ x) := by
  classical
  obtain ⟨a,hdis⟩ := exists_disjoint_planar_translation
    (K₀.isCompact_space_of_finite hK₀) (K₁.isCompact_space_of_finite hK₁)
  have ha := K₁.affineOnFaces_affine a.toContinuousAffineMap
  let J := ha.embeddedImage a.injective.injOn
  have hJ : J.faces.Finite := ha.embeddedImage_finite _ hK₁
  have hJs : J.space = a '' K₁.space := ha.embeddedImage_space _
  let f := K₀.space.piecewise f₀ (f₁ ∘ a.symm)
  have hkeep₀ : EqOn f f₀ K₀.space := by
    intro x hx
    exact piecewise_eq_of_mem _ _ _ hx
  have hkeep₁ (x : P2) (hx : x ∈ K₁.space) : f (a x) = f₁ x := by
    have hn : a x ∉ K₀.space := fun h => disjoint_left.mp hdis h ⟨x,hx,rfl⟩
    simp only [f,piecewise_eq_of_notMem _ _ _ hn,Function.comp_apply,a.symm_apply_apply]
  have hback : PolyhedralPLInCharts e (f₁ ∘ a.symm) J.space :=
    hf₁.comp_finitePiecewiseAffineOn J hJ
      ⟨J,hJ,rfl,J.affineOnFaces_affine a.symm.toContinuousAffineMap⟩ (by
        intro x hx
        obtain ⟨y,hy,rfl⟩ := hJs.subset hx
        simpa only [a.symm_apply_apply] using hy)
  have hfJ : PolyhedralPLInCharts e f J.space := hback.congr (by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hJs.subset hx
    simpa only [Function.comp_apply,a.symm_apply_apply] using (hkeep₁ y hy).symm)
  obtain ⟨L,hL,hLs⟩ := K₀.exists_finite_triangulation_union J hK₀ hJ
  refine ⟨a,L,f,hdis,hL,by rw [hLs,hJs],?_,hkeep₀,hkeep₁⟩
  rw [hLs]
  exact (hf₀.congr hkeep₀.symm).union_of_finite he K₀ J hK₀ hJ hfJ

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
