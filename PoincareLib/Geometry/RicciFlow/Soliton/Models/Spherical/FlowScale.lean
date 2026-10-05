import PoincareLib.Geometry.RicciFlow.Soliton.Basic
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Curvature
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The fixed metric scale of an Einstein shrinking flow

The self-similar slice identifications and Ricci naturality determine the
time derivative on the original manifold. Integrating this scalar equation
removes the time-dependent diffeomorphisms from the metric identity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.ShrinkingSolitonFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData n M}

/-- An Einstein soliton's supplied shrinking flow has a fixed metric scale. -/
theorem inner_eq_neg_time_mul_of_einstein (G : ShrinkingSolitonFlow S)
    (hEinstein : ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
      S.connection.ricci x u v = (1 / 2 : ℝ) * S.metric.inner x u v)
    (t : ℝ) (ht : t < 0) (x : M) (u v : TangentSpace (𝓡 n) x) :
    (G.flow.metric t).inner x u v = (-t) * S.metric.inner x u v := by
  have hder (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun r => (G.flow.metric r).inner x u v)
        ((G.flow.metric s).inner x u v / s) s := by
    obtain ⟨H⟩ := G.self_similar s hs
    have habs : 0 < |s| := abs_pos.mpr hs.ne
    let Ds := rescaledMetric_connection S.metric S.connection |s| habs
    have hR := (G.flow.connection s).ricci_eq_of_local_isometry Ds
      isOpen_univ H.map.contMDiff.contMDiffOn
      (fun y _ a b => by simpa only [rescaledMetric_inner] using H.inner_eq y a b)
      (Set.mem_univ x) u v
    rw [rescaledMetric_ricci, hEinstein] at hR
    have hcoefficient : -2 * (G.flow.connection s).ricci x u v =
        (G.flow.metric s).inner x u v / s := by
      rw [hR, H.inner_eq]
      simp only [abs_of_neg hs]
      field_simp [hs.ne]
    rw [← hcoefficient]
    exact (G.flow.equation s hs x u v).hasDerivAt (isOpen_Iio.mem_nhds hs)
  have hquot (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun r => (G.flow.metric r).inner x u v / r) 0 s := by
    have hd := (hder s hs).div (hasDerivAt_id s) hs.ne
    convert hd using 1 <;> first | rfl | simp [hs.ne]
  have heq := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
    (fun s hs => (hquot s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hquot s hs).deriv) ht (by norm_num : (-1 : ℝ) < 0)
  rw [G.at_minus_one] at heq
  have hmul := (div_eq_iff ht.ne).mp heq
  simpa only [div_neg, div_one, neg_mul, mul_neg, mul_comm] using hmul

end PoincareMT.ShrinkingSolitonFlow
