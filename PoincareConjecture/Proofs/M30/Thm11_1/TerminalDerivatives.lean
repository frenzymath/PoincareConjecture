import PoincareConjecture.Proofs.M30.Thm11_1.ControlledCylinders
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryCurvature
import PoincareConjecture.Proofs.M30.Generalized.TerminalMetric
import PoincareConjecture.Proofs.M30.Thm3_28.FiniteCylinder
import PoincareConjecture.Proofs.M30.Thm3_28.CompactBuffer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem eventually_terminal_curvatureDerivativeNorm_le
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.baseBall k A,
      (RiemannianMetric.leviCivitaData
        (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
          (S.scale k) (S.base_scalar_pos k))).curvatureDerivativeNorm m x ≤ D := by
  let R : ℝ := A + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hAR : A < R := by dsimp [R]; linarith
  obtain ⟨T, hT, B, _hB, hcyl⟩ :=
    exists_radius_dependent_controlled_cylinders hC H hbound R hR
  let ρ : ℝ := (A + R) / 2
  have hρ : 0 < ρ := div_pos (add_pos hA hR) (by norm_num)
  let r : ℝ := (R - A) / (2 * Real.exp ((3 : ℝ) ^ 3 * max B 1 * T))
  have hr : 0 < r := div_pos (sub_pos.mpr hAR) (by positivity)
  obtain ⟨D, hD, hShi⟩ :=
    exists_uniform_curvatureDerivativeNorm_bound_on_buffered_cylinders
      hC.local_derivative_estimates 3 m B T r (T / 2) hT hr (half_pos hT)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hcyl 1 (by norm_num), H.balls_compact ρ hρ] with k he hcompact
  obtain ⟨E⟩ := he
  let C := (S.flow k).slice (S.base k).1
  let g : RiemannianMetric 3 C.carrier := (S.flow k).metric (S.base k).1
  let gbar : RiemannianMetric 3 C.carrier :=
    M13.scaleSmoothMetric g (S.scale k) (S.base_scalar_pos k)
  let : Nonempty C.carrier := ⟨(S.base k).2⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) C.carrier
  have hopen : IsOpen (S.baseBall k R) := by
    change IsOpen {x : C.carrier |
      edist (S.base k).2 x < ENNReal.ofReal (R / Real.sqrt (S.scale k))}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let U : TopologicalSpace.Opens C.carrier := ⟨S.baseBall k R, hopen⟩
  let J : SpacetimeInterval := {
    domain := Icc (-T) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩,
      by linarith⟩ }
  let e : GeneralizedFlowCylinder (S.flow k) C (S.base k).1 (S.scale k) J.domain U :=
    E.embedding
  obtain ⟨G, hG⟩ := Cylinder.exists_ordinaryFlow e (Cylinder.physicalInterval_subset e)
  have h₀ : (0 : ℝ) ∈ J.domain := ⟨by linarith, le_rfl⟩
  have hmetric (x : U) (v w : TangentSpace (𝓡 3) x) :
      (G.metric 0).inner x v w = gbar.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
    rw [hG 0 h₀ x v w,
      Cylinder.pullbackInner_zero_of_identity U.isOpen e h₀
        (E.zero_identity h₀) x.val x.property]
    rfl
  have hcurv (s : ℝ) (hs : s ∈ Icc (-T) 0) (x : U) :
      (G.connection s).curvatureTensorNorm x ≤ B := by
    rw [(Cylinder.curvature_of_ordinaryFlow e G hG s hs x).2]
    apply (div_le_iff₀ (S.base_scalar_pos k)).mpr
    exact (le_abs_self _).trans (E.curvature_bound s hs x.val x.property)
  have hU : (U : Set C.carrier) = gbar.ball (S.base k).2 R :=
    (scaled_terminal_ball_eq_baseBall S k R).symm
  have hballs (r' : ℝ) : gbar.ball (S.base k).2 r' = S.baseBall k r' :=
    scaled_terminal_ball_eq_baseBall S k r'
  have hcompact' : IsCompact (closure (gbar.ball (S.base k).2 ρ)) := by
    rw [hballs]
    exact hcompact
  let V : Set U := (Subtype.val : U → C.carrier) ⁻¹' S.baseBall k A
  have hprecompact (x : U) (hx : x ∈ V) :
      IsCompact (closure ((G.metric (-T)).ball x r)) := by
    apply isCompact_closure_initial_ball_of_terminal_buffer gbar (S.base k).2 U
      hT hA hAR hU G hmetric hcurv hcompact' x
    rw [hballs]
    exact hx
  have hderiv := hShi U G V hprecompact hcurv 0
    (show (0 : ℝ) ∈ Icc (-T + T / 2) 0 from ⟨by linarith, le_rfl⟩)
  have hinv (x : U) :
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x).IsInvertible := by
    have hb := (G.metric 0).mfderiv_bijective_of_pullback_eq gbar x
      (fun v w => (hmetric x v w).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
      exact inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x.val) := by
      exact inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let : T2Space (TangentSpace (𝓡 3) x) :=
      inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin 3)))
    let : T2Space (TangentSpace (𝓡 3) x.val) :=
      inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin 3)))
    exact ⟨LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x).toLinearMap hb), rfl⟩
  intro x hx
  have hxA : x ∈ gbar.ball (S.base k).2 A := by
    rw [hballs]
    exact hx
  have hxU : x ∈ U := by
    change x ∈ (U : Set C.carrier)
    rw [hU]
    exact hxA.trans_le (ENNReal.ofReal_le_ofReal hAR.le)
  let y : U := ⟨x, hxU⟩
  have heq := (G.connection 0).curvatureDerivativeNorm_eq_pullback
    gbar.leviCivitaData isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun z _ => hinv z) (fun z _ v w => hmetric z v w) m (mem_univ y)
  exact heq ▸ hderiv y hx

end PoincareConjecture.M30
