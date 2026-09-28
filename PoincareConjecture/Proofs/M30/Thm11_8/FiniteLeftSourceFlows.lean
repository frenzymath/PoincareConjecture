import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCompactImages
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedSpatialSlices
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftTerminalMap
import PoincareConjecture.Proofs.M30.Generalized.WorldlineUniqueness
import PoincareConjecture.Proofs.M30.Generalized.PullbackCurvature
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ControlledSource
import PoincareConjecture.Proofs.M30.Thm3_28.TerminalSubwindow
import PoincareConjecture.Proofs.M30.Thm5_33.RetainedSourceDefect
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

private theorem openCodomain_localDiffeomorph
    {X : Type*} {Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z]
    (U : TopologicalSpace.Opens Z) (e : X → U)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((Subtype.val : U → Z) ∘ e)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
  have hU := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U
  intro x
  have hix := hU (e x)
  apply ((he x).comp (𝓡 3) U hix.localInverse_isLocalDiffeomorphAt).congr_of_eventuallyEq
  filter_upwards [(he x).contMDiffAt.continuousAt.preimage_mem_nhds
    (hix.localInverse.open_source.mem_nhds hix.localInverse_mem_source)] with y hy
  exact Subtype.ext (hix.localInverse_right_inv hy).symm

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in

theorem exists_extended_source_flows_on_generalized_stage
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (hcompact : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (S.baseBall (G.subsequence k) A)))
    (hcyl : ∀ A : ℝ, 0 < A →
      ∃ delta : ℝ, 0 < delta ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (G.subsequence k)
            A (T + delta) B 1))
    (Y : TopologicalSpace.Opens G.limit.carrier.carrier)
    (hY : IsCompact (closure (Y : Set G.limit.carrier.carrier))) :
    ∃ W delta B : ℝ, 0 < W ∧ 0 < delta ∧ 0 ≤ B ∧ ∃ N : ℕ,
      ∃ E : ∀ k : ℕ, ControlledBlowupCylinder S
          (G.subsequence (k + N)) W (T + delta) B 1,
      ∃ f : ∀ k : ℕ, Y →
          ((S.flow (G.subsequence (k + N))).slice
            (S.base (G.subsequence (k + N))).1).carrier,
      ∃ P : ℕ → RicciFlow 3 Y (Icc (-(T + delta)) 0),
        (∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (f k)) ∧
        (∀ k, closure (Y : Set G.limit.carrier.carrier) ⊆
          G.exhaustion.space (k + N)) ∧
        (∀ k (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time (k + N)) 0) (x : Y),
          (G.embedding (k + N)).pointMap 0 h0 x.val =
            Sigma.mk (S.base (G.subsequence (k + N))).1 (f k x)) ∧
        (∀ k (x : Y), f k x ∈ S.baseBall (G.subsequence (k + N)) W) ∧
        (∀ k s (hs : s ∈ Icc (-(T + delta)) 0) (x : Y)
            (v w : TangentSpace (𝓡 3) x),
          ((P k).metric s).inner x v w =
            (E k).embedding.pullbackInner s hs (f k x)
              (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
              (mfderiv (𝓡 3) (𝓡 3) (f k) x w)) ∧
        (∀ k s (hs : s ∈ Icc (-(T + delta)) 0) (x : Y),
          ((P k).connection s).scalarCurvature x =
              (S.flow (G.subsequence (k + N))).scalar
                ((E k).embedding.pointMap s hs (f k x)) /
                  S.scale (G.subsequence (k + N)) ∧
          ((P k).connection s).curvatureTensorNorm x =
              (S.flow (G.subsequence (k + N))).curvatureNorm
                ((E k).embedding.pointMap s hs (f k x)) /
                  S.scale (G.subsequence (k + N)) ∧
          ((P k).connection s).negativeCurvaturePart x =
              ((S.flow (G.subsequence (k + N))).connection
                ((E k).embedding.pointMap s hs (f k x)).1).negativeCurvaturePart
                  ((E k).embedding.pointMap s hs (f k x)).2 /
                    S.scale (G.subsequence (k + N))) ∧
        (∀ k s (_hs : s ∈ Icc (-(T + delta)) 0)
            (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0)
            (x : Y) (v w : TangentSpace (𝓡 3) x),
          ((P k).metric s).inner x v w =
            (G.embedding (k + N)).pullbackInner s hsG x.val
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : Y → G.limit.carrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : Y → G.limit.carrier.carrier) x w)) ∧
        (∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ k s,
          s ∈ Icc (-(T + delta / 2)) 0 → ∀ x : Y,
            ((P k).connection s).curvatureDerivativeNorm m x ≤ D) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
          ∀ s ∈ Icc (-(T + delta)) 0, ∀ x : Y,
            ((P k).connection s).negativeCurvaturePart x ≤ eta := by
  classical
  obtain ⟨R, hR, himage⟩ :=
    exists_eventually_generalized_terminal_image_baseBall G hY
  let W : ℝ := R + 1
  have hW : 0 < W := by dsimp [W]; linarith
  have hRW : R < W := by dsimp [W]; linarith
  obtain ⟨delta, hdelta, B, hB, hcylW⟩ := hcyl W hW
  have hTdelta : 0 < T + delta := add_pos hT hdelta
  let Gamma : ℝ := (R + W) / 2
  have hGamma : 0 < Gamma := by dsimp [Gamma]; linarith
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G hY
  have htail := hcylW.and ((hcompact Gamma hGamma).and
    (himage.and (eventually_ge_atTop j)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hNk (k : ℕ) := hN (k + N) (by omega)
  let C (k : ℕ) :=
    (S.flow (G.subsequence (k + N))).slice
      (S.base (G.subsequence (k + N))).1
  let gbar (k : ℕ) : RiemannianMetric 3 (C k).carrier :=
    M13.scaleSmoothMetric
      ((S.flow (G.subsequence (k + N))).metric
        (S.base (G.subsequence (k + N))).1)
      (S.scale (G.subsequence (k + N)))
      (S.base_scalar_pos (G.subsequence (k + N)))
  have hballs (k : ℕ) (r : ℝ) :
      (gbar k).ball (S.base (G.subsequence (k + N))).2 r =
        S.baseBall (G.subsequence (k + N)) r := by
    exact scaled_terminal_ball_eq_baseBall S (G.subsequence (k + N)) r
  let U (k : ℕ) : TopologicalSpace.Opens (C k).carrier :=
    ⟨S.baseBall (G.subsequence (k + N)) W,
      baseBall_isOpen S (G.subsequence (k + N)) W⟩
  let E (k : ℕ) : ControlledBlowupCylinder S
      (G.subsequence (k + N)) W (T + delta) B 1 :=
    Classical.choice (hNk k).1
  have hsource (k : ℕ) := exists_controlled_ordinary_source (E k) hW hTdelta
  let Fsrc (k : ℕ) : RicciFlow 3 (U k) (Icc (-(T + delta)) 0) :=
    Classical.choose (hsource k)
  have hsrc (k : ℕ) := (Classical.choose_spec (hsource k)).1
  have hterminal (k : ℕ) := (Classical.choose_spec (hsource k)).2.1
  have hstage (k : ℕ) : closure (Y : Set G.limit.carrier.carrier) ⊆
      G.exhaustion.space (k + N) := by
    intro x hx
    exact G.exhaustion.space_increasing (hNk k).2.2.2 (hj hx)
  have hzero (k : ℕ) : (0 : ℝ) ∈ Icc (-G.exhaustion.time (k + N)) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos _).le, le_rfl⟩
  choose dSpatial hdsource hpointAmbient using fun k : ℕ =>
    exists_generalized_terminal_partialDiffeomorph G (k + N)
  let f (k : ℕ) : Y → (C k).carrier := fun x => dSpatial k x.val
  have hpoint (k : ℕ) (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time (k + N)) 0)
      (x : Y) : (G.embedding (k + N)).pointMap 0 h0 x.val =
        (⟨(S.base (G.subsequence (k + N))).1, f k x⟩ :
          (S.flow (G.subsequence (k + N))).point) := hpointAmbient k h0 x.val
  have hfambient (k : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (f k) := by
    intro x
    have hxsource : x.val ∈ (dSpatial k).source := by
      rw [hdsource k]
      exact hstage k (subset_closure x.property)
    have hloc := (dSpatial k).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      hxsource
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y x).comp
      (𝓡 3) (C k).carrier hloc
  have hfxR (k : ℕ) (x : Y) : f k x ∈ S.baseBall
      (G.subsequence (k + N)) R := by
    obtain ⟨y, hy, heq⟩ := (hNk k).2.2.1 x (subset_closure x.property)
    have hxy : f k x = y := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        ((hpoint k (hzero k) x).symm.trans (heq (hzero k)))).2
    simpa only [hxy] using hy
  have hfx (k : ℕ) (x : Y) : f k x ∈ S.baseBall
      (G.subsequence (k + N)) W := by
    have hy := hfxR k x
    rw [← hballs k W]
    rw [← hballs k R] at hy
    change (gbar k).edist (S.base (G.subsequence (k + N))).2 (f k x) < ENNReal.ofReal W
    change (gbar k).edist (S.base (G.subsequence (k + N))).2 (f k x) < ENNReal.ofReal R at hy
    exact hy.trans_le (ENNReal.ofReal_mono hRW.le)
  have himageU (k : ℕ) (x : Y) : f k x ∈ (U k : Set (C k).carrier) := hfx k x
  let eU (k : ℕ) : Y → U k := fun x => ⟨f k x, himageU k x⟩
  have hfU (k : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (eU k) := by
    apply openCodomain_localDiffeomorph (U k) (eU k)
    change IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (f k)
    exact hfambient k
  let P (k : ℕ) : RicciFlow 3 Y (Icc (-(T + delta)) 0) :=
    (Fsrc k).pullbackWithConnection (eU k) (hfU k)
      (fun s => (((Fsrc k).metric s).pullbackOfLocalDiffeomorph
        (eU k) (hfU k)).leviCivitaData)
  have hPmetric (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-(T + delta)) 0)
      (x : Y) (v w : TangentSpace (𝓡 3) x) :
      ((P k).metric s).inner x v w =
        (E k).embedding.pullbackInner s hs (f k x)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x w) := by
    have he : ContMDiff (𝓡 3) (𝓡 3) ∞ (eU k) := (hfU k).contMDiff
    have hd := mfderiv_comp x
      (contMDiff_subtype_val (n := ∞) (eU k x) |>.mdifferentiableAt (by simp))
      ((he x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (f k) x =
      (mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : U k → (C k).carrier) (eU k x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (eU k) x) at hd
    change (((Fsrc k).metric s).pullbackOfLocalDiffeomorph
        (eU k) (hfU k)).inner x v w = _
    rw [RiemannianMetric.pullbackOfLocalDiffeomorph_inner,
      hsrc k s hs (eU k x)]
    rw [hd]
    rfl
  have hmeet (k : ℕ) (x : Y) :
      (E k).embedding.pointMap 0 (by constructor <;> linarith [hTdelta]) (f k x) =
        (G.embedding (k + N)).pointMap 0 (hzero k) x.val := by
    rw [(E k).zero_identity _ (f k x) (hfx k x)]
    exact (hpoint k (hzero k) x).symm
  have hmap_eq (k : ℕ) (s : ℝ)
      (hs : s ∈ Icc (-(T + delta)) 0)
      (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0) (x : Y) :
      (E k).embedding.pointMap s hs (f k x) =
        (G.embedding (k + N)).pointMap s hsG x.val := by
    have hall := Cylinder.pointMap_eq_on_overlap (E k).embedding
      (G.embedding (k + N)) ordConnected_Icc ordConnected_Icc
      (hfx k x) (hstage k (subset_closure x.property))
      (s := 0) (by constructor <;> linarith) (hzero k) (hmeet k x)
    exact hall s hs hsG
  have hGmetric (k : ℕ) (s : ℝ)
      (hs : s ∈ Icc (-(T + delta)) 0)
      (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0)
      (x : Y) (v w : TangentSpace (𝓡 3) x) :
      ((P k).metric s).inner x v w =
        (G.embedding (k + N)).pullbackInner s hsG x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : Y → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : Y → G.limit.carrier.carrier) x w) := by
    have hfun : (fun y : Y => (E k).embedding.forward s hs (f k y)) =
        (fun y : Y => (G.embedding (k + N)).forward s hsG y.val) := by
      funext y
      exact eq_of_heq (Sigma.mk.inj_iff.mp (hmap_eq k s hs hsG y)).2
    have hEforward := (E k).embedding.forward_smooth s hs
    have hGforward := (G.embedding (k + N)).forward_smooth s hsG
    have hEAt :=
      (hEforward.contMDiffAt ((U k).isOpen.mem_nhds (hfx k x))).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
    have hfAt :=
      (hfambient k x).contMDiffAt.mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
    have hEcomp := mfderiv_comp_apply x
      hEAt hfAt
    have hGAt :=
      (hGforward.contMDiffAt
        ((G.exhaustion.space_open (k + N)).mem_nhds
          (hstage k (subset_closure x.property)))).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
    have hsubAt :=
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y x).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
    have hGcomp := mfderiv_comp_apply x hGAt hsubAt
    have hread := congrArg (fun z : Y →
        ((S.flow (G.subsequence (k + N))).slice
          ((S.base (G.subsequence (k + N))).1 +
            s / S.scale (G.subsequence (k + N)))).carrier =>
      S.scale (G.subsequence (k + N)) *
        ((S.flow (G.subsequence (k + N))).metric
          ((S.base (G.subsequence (k + N))).1 +
            s / S.scale (G.subsequence (k + N)))).inner (z x)
          (mfderiv (𝓡 3) (𝓡 3) z x v) (mfderiv (𝓡 3) (𝓡 3) z x w)) hfun
    simp only [Function.comp_def] at hEcomp hGcomp
    rw [hEcomp v, hEcomp w, hGcomp v, hGcomp w] at hread
    rw [hPmetric k s hs x v w]
    exact hread
  let J : SpacetimeInterval := {
    domain := Icc (-(T + delta)) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-(T + delta), ⟨le_rfl, by linarith⟩, 0,
      ⟨by linarith, le_rfl⟩, by linarith⟩ }
  have hscalar (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-(T + delta)) 0)
      (x : Y) :
      ((P k).connection s).scalarCurvature x =
        (S.flow (G.subsequence (k + N))).scalar
          ((E k).embedding.pointMap s hs (f k x)) /
          S.scale (G.subsequence (k + N)) := by
    exact (Cylinder.curvature_of_pullbackFlow (C := C k) (U := U k) (J := J)
      (E k).embedding (f k)
      (hfambient k).contMDiff (himageU k) (P k) (hPmetric k) s hs x).1
  have hcurvRead (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-(T + delta)) 0)
      (x : Y) :
      ((P k).connection s).curvatureTensorNorm x =
        (S.flow (G.subsequence (k + N))).curvatureNorm
          ((E k).embedding.pointMap s hs (f k x)) /
          S.scale (G.subsequence (k + N)) ∧
      ((P k).connection s).negativeCurvaturePart x =
        ((S.flow (G.subsequence (k + N))).connection
          ((E k).embedding.pointMap s hs (f k x)).1).negativeCurvaturePart
            ((E k).embedding.pointMap s hs (f k x)).2 /
              S.scale (G.subsequence (k + N)) := by
    have h := Cylinder.curvature_of_pullbackFlow (C := C k) (U := U k) (J := J)
      (E k).embedding (f k)
      (hfambient k).contMDiff (himageU k) (P k) (hPmetric k) s hs x
    exact ⟨h.2.1, h.2.2⟩
  have hphi : StrictMono (fun k : ℕ => G.subsequence (k + N)) :=
    G.subsequence_strictMono.comp (fun _ _ h => Nat.add_lt_add_right h N)
  have hdefect (eta : ℝ) (heta : 0 < eta) : ∀ᶠ k : ℕ in atTop,
      ∀ s ∈ Icc (-(T + delta)) 0, ∀ x : Y,
        ((P k).connection s).negativeCurvaturePart x ≤ eta := by
    exact eventually_retained_source_negativeDefect_le S hbranch
      (fun k => G.subsequence (k + N)) hphi hTdelta hB E f
      (Eventually.of_forall fun k => (hfambient k).contMDiff) hfx P hPmetric eta heta
  have hcurvSrc (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-(T + delta)) 0)
      (x : U k) : ((Fsrc k).connection s).curvatureTensorNorm x ≤ B := by
    rw [(Cylinder.curvature_of_ordinaryFlow (C := C k) (U := U k) (J := J)
      (E k).embedding (Fsrc k)
      (hsrc k) s hs x).2]
    apply (div_le_iff₀ (S.base_scalar_pos (G.subsequence (k + N)))).mpr
    exact (le_abs_self _).trans ((E k).curvature_bound s hs x.val x.property)
  refine ⟨W, delta, B, hW, hdelta, hB, N, E, f, P, hfambient, hstage, hpoint,
    hfx, hPmetric, ?_, hGmetric, ?_, hdefect⟩
  · intro k s hs x
    exact ⟨hscalar k s hs x, hcurvRead k s hs x⟩
  · intro m
    obtain ⟨D, hD, hbound⟩ :=
      exists_uniform_curvatureDerivativeNorm_bound_on_terminal_subwindow
        hShi 3 m B (T + delta) (T + delta / 2) R W
          (by linarith) (by linarith) hR hRW
    refine ⟨D, hD.le, ?_⟩
    intro k s hs x
    have hcompactK : IsCompact (closure ((gbar k).ball
        (S.base (G.subsequence (k + N))).2 Gamma)) := by
      rw [hballs k Gamma]
      exact (hNk k).2.1
    have hsourcebound := hbound (C k).carrier (gbar k)
      (S.base (G.subsequence (k + N))).2 (U k)
      (by exact (hballs k W).symm) (Fsrc k) (hterminal k) (hcurvSrc k)
      hcompactK s hs (eU k x) (by
        rw [hballs k R]
        exact hfxR k x)
    have hnorm := ((P k).connection s).curvatureDerivativeNorm_eq_pullback
      ((Fsrc k).connection s) isOpen_univ (hfU k).contMDiff.contMDiffOn
      (fun y _ => ⟨(hfU k y).mfderivToContinuousLinearEquiv (by simp), rfl⟩)
      (fun _ _ _ _ => rfl) m (mem_univ x)
    rw [hnorm]
    exact hsourcebound

end PoincareConjecture.M30
