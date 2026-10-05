import PoincareLib.Geometry.Spacetime.Rescaling.Time

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13AtlasRescaling.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Exact affine rescaling of a raw adapted atlas

Morgan-Tian Definition 3.40, p. 61, on the adapted presentations of
Definitions 3.34-3.35, pp. 59-60. This is construction output: the new atlas
has the same carrier, box indices, spatial domains and spatial transitions.
Only its clock and metric coefficients change. No existence is built into a
definition or supplied as a premise of the full M13 theorem.
-/

set_option autoImplicit false

open scoped Topology

universe u

namespace PoincareMT

/-- An actual raw rescaled atlas with its prescribed maps and coefficients. -/
structure ParabolicAtlasRescaling {n : ℕ} {X : Type u} [TopologicalSpace X]
    (A : AdaptedMetricAtlas n X) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) where
  atlas : AdaptedMetricAtlas n X
  time_eq : atlas.time = fun p ↦ parabolicTime Q a (A.time p)
  interval_eq : atlas.interval = parabolicInterval Q hQ a A.interval
  box_index_eq : atlas.box_index = A.box_index
  box_interval : ∀ b : A.box_index,
    (atlas.box (cast box_index_eq.symm b)).interval =
      parabolicInterval Q hQ a (A.box b).interval
  box_spatial : ∀ b : A.box_index,
    (atlas.box (cast box_index_eq.symm b)).spatial = (A.box b).spatial
  box_map : ∀ (b : A.box_index) (t : (A.box b).interval.domain)
    (x : (A.box b).spatial),
    (atlas.box (cast box_index_eq.symm b)).toSpacetime
      (⟨parabolicTime Q a t.val, by
        rw [box_interval b]
        exact (parabolicTime_mem_parabolicInterval_iff Q hQ a
          (A.box b).interval t.val).2 t.property⟩,
       ⟨x.val, by rw [box_spatial b]; exact x.property⟩) =
      (A.box b).toSpacetime (t, x)
  metric_eq : ∀ (b : A.box_index) (t : ℝ) (x v w : EuclideanSpace ℝ (Fin n)),
    (atlas.box (cast box_index_eq.symm b)).metric (t, x) v w =
      Q * (A.box b).metric (parabolicTimeInv Q a t, x) v w
  transition_transport : ∀ (b c : A.box_index) (t : ℝ)
    (x y : EuclideanSpace ℝ (Fin n))
    (θ : AdaptedMetricTransition (A.box b) (A.box c) t x y),
    ∃ θ' : AdaptedMetricTransition
        (atlas.box (cast box_index_eq.symm b))
        (atlas.box (cast box_index_eq.symm c)) (parabolicTime Q a t) x y,
      θ'.coordinateChange = θ.coordinateChange ∧
      θ'.interval = parabolicInterval Q hQ a θ.interval

end PoincareMT
