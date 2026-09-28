import PoincareConjecture.Proofs.M76.Mathlib.RelativeManifoldPLApproximation
import PoincareConjecture.Proofs.M76.Mathlib.SimplyConnectedDiskPairExtension

set_option autoImplicit false

open Set Geometry

namespace Geometry

theorem PolyhedralPLInCharts.congr
    {E F M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M F} {f g : E → M} {S : Set E}
    (hf : PolyhedralPLInCharts e f S) (hfg : EqOn f g S) :
    PolyhedralPLInCharts e g S := by
  refine ⟨hf.continuousOn.congr hfg.symm, ?_⟩
  intro x
  obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hfJ, hcoords⟩ := hf.coordinates x
  refine ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, ?_, ?_⟩
  · intro y hy
    rw [← hfg (hJS hy)]
    exact hfJ hy
  · exact hcoords.congr (fun y hy => congrArg (e i) (hfg (hJS hy)))

end Geometry

namespace OpenPartialHomeomorph

theorem exists_polyhedralPL_disk_extension
    {E F M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [T2Space M]
    [LocallyCompactSpace M]
    (e : ι → OpenPartialHomeomorph M F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hball : IsUnitBallPair ℂ K.space L.space)
    {b : E → M} (hb : PolyhedralPLInCharts e b L.space)
    {W : Set M} (hW : IsOpen W) (hsc : IsSimplyConnected W)
    (hbW : MapsTo b L.space W) :
    ∃ q : E → M, PolyhedralPLInCharts e q K.space ∧ EqOn q b L.space ∧
      MapsTo q K.space W := by
  classical
  let : SimplyConnectedSpace W := hsc
  let bW : C(L.space, W) :=
    ⟨fun x => ⟨b x, hbW x.property⟩,
      hb.continuousOn.domRestrict.subtype_mk (fun x => hbW x.property)⟩
  obtain ⟨G, hG⟩ := hball.exists_continuous_disk_extension bW
  let f : E → M := fun x => if hx : x ∈ K.space then (G ⟨x, hx⟩ : M) else b x
  have hf (x : E) (hx : x ∈ K.space) : f x = (G ⟨x, hx⟩ : M) := by
    dsimp only [f]
    rw [dif_pos hx]
  have hfc : ContinuousOn f K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp G.continuous).congr
      (fun x => (hf x x.property).symm)
  have hfW : MapsTo f K.space W := by
    intro x hx
    rw [hf x hx]
    exact (G ⟨x, hx⟩).property
  have hfb : EqOn f b L.space := by
    intro x hx
    rw [hf x (hball.1 hx)]
    exact congrArg Subtype.val (hG ⟨x, hx⟩)
  have hfL : PolyhedralPLInCharts e f L.space := hb.congr hfb.symm
  obtain ⟨q, hq, hqf, hqW, _⟩ := exists_relative_polyhedralPL_approximation
    e hcompat hcover K L hK hL hball.1 hfc hfL hW hfW
  exact ⟨q, hq, hqf.trans hfb, hqW⟩

end OpenPartialHomeomorph
