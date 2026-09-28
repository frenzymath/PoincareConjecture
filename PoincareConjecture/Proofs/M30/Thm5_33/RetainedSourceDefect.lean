import PoincareConjecture.Proofs.M30.Generalized.PullbackCurvature
import PoincareConjecture.Proofs.M30.Thm5_33.NegativeDefect
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ControlledSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M30

theorem eventually_retained_source_negativeDefect_le
    (S : GeneralizedBlowupSequence.{u})
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) {W T B eta₀ : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B)
    (E : ∀ k, ControlledBlowupCylinder S (phi k) W T B eta₀)
    {Y : Type v} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
    (f : ∀ k, Y → ((S.flow (phi k)).slice (S.base (phi k)).1).carrier)
    (hf : ∀ᶠ k in atTop, ContMDiff (𝓡 3) (𝓡 3) ∞ (f k))
    (himage : ∀ k x, f k x ∈ S.baseBall (phi k) W)
    (G : ℕ → RicciFlow 3 Y (Icc (-T) 0))
    (hG : ∀ k s (hs : s ∈ Icc (-T) 0) (x : Y) (v w : TangentSpace (𝓡 3) x),
      ((G k).metric s).inner x v w = (E k).embedding.pullbackInner s hs (f k x)
        (mfderiv (𝓡 3) (𝓡 3) (f k) x v) (mfderiv (𝓡 3) (𝓡 3) (f k) x w))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ s ∈ Icc (-T) 0, ∀ x : Y,
      ((G k).connection s).negativeCurvaturePart x ≤ eta := by
  let J : SpacetimeInterval := {
    domain := Icc (-T) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩,
      by linarith⟩ }
  filter_upwards [hf, hphi.tendsto_atTop.eventually
    (eventually_negativeDefect_le S hbranch (9 * B) (by positivity) eta heta)]
      with k hfk hk s hs x
  let U : TopologicalSpace.Opens ((S.flow (phi k)).slice (S.base (phi k)).1).carrier :=
    ⟨S.baseBall (phi k) W, baseBall_isOpen S (phi k) W⟩
  have hread := Cylinder.curvature_of_pullbackFlow (J := J) (U := U)
    (E k).embedding (f k) hfk (himage k) (G k) (hG k) s hs x
  rw [hread.2.2]
  apply (div_le_iff₀ (S.base_scalar_pos (phi k))).mpr
  let p := (E k).embedding.pointMap s hs (f k x)
  apply hk p.1 (((S.flow (phi k)).slice_nonempty_iff p.1).mp ⟨p.2⟩) p.2
  have hnorm : (S.flow (phi k)).curvatureNorm p ≤ B * S.scale (phi k) :=
    (le_abs_self _).trans ((E k).curvature_bound s hs (f k x) (himage k x))
  have hscalar := ((S.flow (phi k)).connection p.1).abs_scalarCurvature_le_curvatureTensorNorm
    p.2
  norm_num only [Nat.cast_ofNat, Nat.reducePow] at hscalar
  calc
    (S.flow (phi k)).scalar p ≤ 9 * (S.flow (phi k)).curvatureNorm p :=
      (le_abs_self _).trans hscalar
    _ ≤ 9 * (B * S.scale (phi k)) := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = (9 * B) * S.scale (phi k) := by ring

end PoincareConjecture.M30
