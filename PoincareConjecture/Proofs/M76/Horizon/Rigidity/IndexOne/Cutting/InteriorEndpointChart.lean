import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.ChartRestriction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleEndpointHalfspace

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_interior_circle_endpoint_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (p : ℝ) [Fact (0 < p)] {R : Set X} (q : R → AddCircle p)
    {a b theta d : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (htheta : theta = a ∨ theta = b) (hd : (d : AddCircle p) = (theta : AddCircle p))
    (ell : E →ᴬ[ℝ] ℝ) (v : E) (T : OpenPartialHomeomorph X E)
    (hlv : ell.contLinear v = 1) {x : X} (hx : x ∈ T.source)
    (hlx : ell (T x) = 0) (hTR : T.source ⊆ R)
    (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E)
    (hq : ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d : ℝ) : AddCircle p)) :
    ∃ (lambda : E →ᴬ[ℝ] ℝ) (w : E) (G : OpenPartialHomeomorph X E),
      lambda.contLinear w = 1 ∧ x ∈ G.source ∧ G.source ⊆ T.source ∧
      lambda (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      ∀ y ∈ G.source,
        (∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
          0 ≤ lambda (G y) := by
  classical
  let q' : X → AddCircle p := fun y => if hy : y ∈ R then q ⟨y, hy⟩ else 0
  have hq' (y : X) (hy : y ∈ T.source) :
      q' y = ((ell (T y) + d : ℝ) : AddCircle p) := by
    simpa only [q', dif_pos (hTR hy)] using hq ⟨y, hTR hy⟩ hy
  obtain ⟨lambda, w, G0, hlw, hxG, hlxG, hG0, hhalf⟩ :=
    OpenPartialHomeomorph.exists_circle_endpoint_halfspace e p q'
      ha hab hb htheta hd ell v T hlv hx hlx hT hq'
  obtain ⟨G, hGs, hGG, hG⟩ := exists_compatible_chart_restriction e G0 hG0 T.open_source
  refine ⟨lambda, w, G, hlw, hGs.symm.subset ⟨hxG, hx⟩,
    hGs.subset.trans inter_subset_right, ?_, hG, ?_⟩
  · rw [hGG]
    exact hlxG
  · intro y hy
    have hy0 := (hGs.subset hy).1
    have hyR := hTR (hGs.subset hy).2
    rw [hGG, ← hhalf y hy0]
    change (∃ h : y ∈ R, q ⟨y, h⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
      q' y ∈ AddCircle.closedIntervalArc p a b
    simp only [q', dif_pos hyR]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hyR, h⟩⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
