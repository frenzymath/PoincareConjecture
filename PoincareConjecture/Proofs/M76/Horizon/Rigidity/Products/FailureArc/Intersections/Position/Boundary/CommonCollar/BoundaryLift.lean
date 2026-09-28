import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_original_collar_boundary_lift
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {K : Set E} {B : Set X} (HB : K ≃ₜ B) {a : ℝ} (ha : 0 ≤ a)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (K ×ˢ Icc (0 : ℝ) a))
    (hi : InjOn c (K ×ˢ Icc (0 : ℝ) a))
    (hbase : ∀ x : K, c (x, 0) = HB x)
    (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite)
    (f : Z → X) (hf : PolyhedralPLInCharts e f A.space) (hfB : MapsTo f A.space B) :
    ∃ rim : Z → E, FinitePiecewiseAffineOn rim A.space ∧
      MapsTo rim A.space K ∧ ∀ z ∈ A.space, c (rim z, 0) = f z := by
  classical
  let rim (z : Z) : E := if hz : z ∈ A.space then HB.symm ⟨f z, hfB hz⟩ else 0
  have hrim (z : Z) (hz : z ∈ A.space) : rim z = (HB.symm ⟨f z, hfB hz⟩ : E) := by
    simp only [rim, dif_pos hz]
  have hrimK : MapsTo rim A.space K := by
    intro z hz
    rw [hrim z hz]
    exact (HB.symm ⟨f z, hfB hz⟩).property
  have hrimc : ContinuousOn rim A.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : A.space => rim z)
    have heq : (fun z : A.space => rim z) =
        (fun z : A.space => (HB.symm ⟨f z, hfB z.property⟩ : E)) := by
      funext z
      exact hrim z z.property
    rw [heq]
    exact continuous_subtype_val.comp (HB.symm.continuous.comp
      (hf.continuousOn.domRestrict.subtype_mk _))
  have hb (z : Z) (hz : z ∈ A.space) : c (rim z, 0) = f z := by
    rw [hrim z hz, hbase]
    exact congrArg Subtype.val (HB.apply_symm_apply ⟨f z, hfB hz⟩)
  have hcomp : PolyhedralPLInCharts e (fun z => c (rim z, 0)) A.space :=
    hf.congr (fun z hz => (hb z hz).symm)
  have hpair : FinitePiecewiseAffineOn (fun z => (rim z, (0 : ℝ))) A.space :=
    hc.finitePiecewiseAffineOn_lift hcompat hi A hA
      (hrimc.prodMk continuous_const.continuousOn) (fun _ hz => ⟨hrimK hz, le_rfl, ha⟩) hcomp
  exact ⟨rim, hpair.postcomp (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap, hrimK, hb⟩

end PoincareConjecture.M76
