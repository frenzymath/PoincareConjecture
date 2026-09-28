import PoincareConjecture.Proofs.M03.ConnectionExistence
import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative
import PoincareConjecture.Proofs.M03.Existence.PullbackMetricFamilyNative
import PoincareConjecture.Proofs.M03.Existence.PullbackMetricDerivativeNative
import PoincareConjecture.Proofs.M03.Existence.PullbackConnectionNative
import PoincareConjecture.Proofs.M03.Existence.ConjugatorPullbackDerivativeNative
import PoincareConjecture.Proofs.M03.CurvatureTrace
import PoincareConjecture.Proofs.M03.ConnectionFamily
import PoincareConjecture.Proofs.M03.Existence.GaugeRecovery
import PoincareConjecture.Proofs.M03.Existence.IntegralGaugeFTCNative
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle

noncomputable section

universe u

namespace PoincareConjecture.MetricFamilyProducerNative

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

def connection (g : RiemannianMetric n M) : LeviCivitaData g :=
  Classical.choice (exists_leviCivitaData g)

def deTurckField (g0 g : RiemannianMetric n M)
    (x : M) : TangentSpace (𝓡 n) x :=
  DeTurckNative.intrinsicDeTurckField (connection g) (connection g0) x

theorem contMDiffOn_deTurckField {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (g0 : RiemannianMetric n M) (hg : RiemannianMetric.IsSmoothFamilyOn g J) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : ℝ × M => (⟨q.2, deTurckField g0 (g q.1) q.2⟩ :
        TangentBundle (𝓡 n) M)) (J ×ˢ Set.univ) := by
  classical
  intro p hp
  let F := DeTurckNative.chartFrame (n := n) p.2
  let U := (chartAt (EuclideanSpace ℝ (Fin n)) p.2).source
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2
  have hU : IsOpen U := (chartAt (EuclideanSpace ℝ (Fin n)) p.2).open_source
  have hpU : p.2 ∈ U := mem_chart_source (EuclideanSpace ℝ (Fin n)) p.2
  have hF (a : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) U :=
    DeTurckNative.chartFrame_contMDiffOn p.2 a
  have hsmall : J ×ˢ U ∈ 𝓝[J ×ˢ Set.univ] p := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU))] with q hq hqU
    exact ⟨hq.1, hqU⟩
  have hbase : ∀ᶠ q in 𝓝[J ×ˢ U] p, q.2 ∈ e.baseSet :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (continuous_snd.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p.2)))
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun q : ℝ × M => fun a c => (g q.1).inner q.2 (F a q.2) (F c q.2))
      (J ×ˢ U) := by
    apply contMDiffOn_pi_space.mpr
    intro a
    apply contMDiffOn_pi_space.mpr
    intro c
    exact Proofs.M03.contMDiffOn_family_metric_pair hg (F a) (F c) (hF a) (hF c)
  have hdet : (DeTurckNative.frameMetricJet (g p.1) F p.2).value.det ≠ 0 :=
    ne_of_gt (DeTurckNative.frameMetricJet_value_posDef (g p.1) F p.2
      (DeTurckNative.chartFrameBasis p.2 p.2 hpU)
      (DeTurckNative.chartFrame_eq_basis p.2 p.2 hpU)).det_pos
  have hI :=
    (DeTurckNative.contDiffAt_matrixInverseEntries_infty
      (fun a c => (g p.1).inner p.2 (F a p.2) (F c p.2)) hdet).contMDiffAt
      |>.comp_contMDiffWithinAt p (hG p ⟨hp.1, hpU⟩)
  have hcoord {g' : ℝ → RiemannianMetric n M}
      (h : RiemannianMetric.IsSmoothFamilyOn g' J)
      (D : (t : ℝ) → LeviCivitaData (g' t)) (a c : Fin n) :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun q : ℝ × M =>
          (e (⟨q.2, (D q.1).connection (F c) q.2 (F a q.2)⟩ :
            TangentBundle (𝓡 n) M)).2) (J ×ˢ U) p := by
    have hconn := Proofs.M03.contMDiffOn_connection_family h D hU (F c) (hF c)
    have hfield : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun q : ℝ × M => (⟨q.2, F a q.2⟩ : TangentBundle (𝓡 n) M))
        (J ×ˢ U) :=
      (hF a).comp contMDiffOn_snd (fun _ hq => hq.2)
    have heval := ContMDiffOn.clm_bundle_apply
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (b := fun q : ℝ × M => q.2)
      (ϕ := fun q : ℝ × M => (D q.1).connection (F c) q.2) hconn hfield
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval p ⟨hp.1, hpU⟩)).2
  have hbackground : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g0) J :=
    (g0.contMDiff.comp contMDiff_snd).contMDiffOn
  have hterm (a c : Fin n) :=
    (contMDiffWithinAt_pi_space.mp (contMDiffWithinAt_pi_space.mp hI a) c).smul
      ((hcoord hg (fun t => connection (g t)) a c).sub
        (hcoord hbackground (fun _ => connection g0) a c))
  have hsum := contMDiffWithinAt_finsetSum fun a (_ : a ∈ Finset.univ) =>
    contMDiffWithinAt_finsetSum fun c (_ : c ∈ Finset.univ) => hterm a c
  have hlocal : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : ℝ × M => (⟨q.2, deTurckField g0 (g q.1) q.2⟩ :
        TangentBundle (𝓡 n) M)) (J ×ˢ U) p := by
    apply Bundle.contMDiffWithinAt_totalSpace.mpr
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    apply hsum.congr_of_eventuallyEq_of_mem _ ⟨hp.1, hpU⟩
    filter_upwards [self_mem_nhdsWithin, hbase] with q hq hqe
    change (e (⟨q.2, deTurckField g0 (g q.1) q.2⟩ : TangentBundle (𝓡 n) M)).2 = _
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hqe]
    unfold deTurckField
    rw [DeTurckNative.intrinsicDeTurckField_eq_frame_contraction
      (connection (g q.1)) (connection g0) F q.2
      (DeTurckNative.chartFrameBasis p.2 q.2 hq.2)
      (DeTurckNative.chartFrame_eq_basis p.2 q.2 hq.2)]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [DeTurckNative.connectionDifference_apply_field
      (connection (g q.1)) (connection g0)
      (((hF c q.2 hq.2).contMDiffAt (hU.mem_nhds hq.2)).mdifferentiableAt (by simp)),
      map_sub, e.continuousLinearMapAt_apply_of_mem ℝ hqe,
      e.continuousLinearMapAt_apply_of_mem ℝ hqe]
    rfl
  exact hlocal.mono_of_mem_nhdsWithin hsmall

def lieTerm (g0 g : RiemannianMetric n M) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  DeTurckNative.metricLieDerivative (connection g) (deTurckField g0 g) x u v

def deTurckRHS (g0 g : RiemannianMetric n M) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  -2 * (connection g).ricci x u v + lieTerm g0 g x u v

def pulledSource {g0 : RiemannianMetric n M} {J : Set ℝ}
    (P : PullbackMetricFamilyData J g0) (t : ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  deTurckRHS g0 (P.baseMetric t) (P.diffeo t x)
    (mfderiv (𝓡 n) (𝓡 n) (P.diffeo t) x u)
    (mfderiv (𝓡 n) (𝓡 n) (P.diffeo t) x v)

def pulledLie {g0 : RiemannianMetric n M} {J : Set ℝ}
    (P : PullbackMetricFamilyData J g0) (t : ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  lieTerm g0 (P.baseMetric t) (P.diffeo t x)
    (mfderiv (𝓡 n) (𝓡 n) (P.diffeo t) x u)
    (mfderiv (𝓡 n) (𝓡 n) (P.diffeo t) x v)

theorem contDiffOn_metric_evaluation {g : ℝ → RiemannianMetric n M}
    {J : Set ℝ} (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞ (fun t => (g t).inner x u v) J := by
  have hsection := hg.comp
    (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
    (show Set.MapsTo (fun t : ℝ => (t, x)) J (J ×ˢ Set.univ) from
      fun _ ht => ⟨ht, Set.mem_univ x⟩)
  have hpair := ContMDiffOn.clm_bundle_apply₂
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    (F₃ := ℝ) (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
    (E₃ := fun _ : M => ℝ) (b := fun _ : ℝ => x)
    (ψ := fun t => (g t).inner x) hsection
    (contMDiffOn_const (c := (⟨x, u⟩ : TangentBundle (𝓡 n) M)))
    (contMDiffOn_const (c := (⟨x, v⟩ : TangentBundle (𝓡 n) M)))
  apply ContMDiffOn.contDiffOn
  intro t ht
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair t ht)).2

theorem contMDiffOn_diffeomorph_pushforward {J : Set ℝ}
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (J ×ˢ Set.univ))
    (x : M) (u : TangentSpace (𝓡 n) x) :
    ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun t => (⟨Phi t x, mfderiv (𝓡 n) (𝓡 n) (Phi t) x u⟩ :
        TangentBundle (𝓡 n) M)) J := by
  intro t ht
  have hPhiAt := hPhi (t, x) ⟨ht, Set.mem_univ x⟩
  have hd := ContMDiffWithinAt.mfderivWithin
    (n := ∞) (m := ∞) (f := fun s (y : M) => Phi s y) (g := fun _ : ℝ => x)
    hPhiAt contMDiffWithinAt_const ht (fun _ _ => Set.mem_univ x)
    (by simp) uniqueMDiffOn_univ
  have horbit : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun s => Phi s x) J t :=
    hPhiAt.comp t (f := fun s : ℝ => (s, x))
      (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
      (fun _ hs => ⟨hs, Set.mem_univ x⟩)
  have hu := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := 𝓡 n) (IB₂ := 𝓡 n) (IM := 𝓘(ℝ, ℝ))
    (b₁ := fun _ : ℝ => x) (b₂ := fun s => Phi s x) hd
    (contMDiffWithinAt_const (c := (⟨x, u⟩ : TangentBundle (𝓡 n) M))) horbit
  simpa only [mfderivWithin_univ] using hu

theorem contDiffOn_twoTimeEvaluation {J : Set ℝ}
    (g : ℝ → RiemannianMetric n M)
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (J ×ˢ Set.univ))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => (g q.1).inner (Phi q.2 x)
        (mfderiv (𝓡 n) (𝓡 n) (Phi q.2) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Phi q.2) x v)) (J ×ˢ J) := by
  have horbit : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t => Phi t x) J :=
    hPhi.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun _ ht => ⟨ht, Set.mem_univ x⟩)
  have hfst : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      Prod.fst (J ×ˢ J) := contDiff_fst.contMDiff.contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      Prod.snd (J ×ˢ J) := contDiff_snd.contMDiff.contMDiffOn
  have hmap : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun q : ℝ × ℝ => (q.1, Phi q.2 x)) (J ×ˢ J) :=
    hfst.prodMk (horbit.comp hsnd (fun _ hq => hq.2))
  have hmetric := hg.comp hmap (fun _ hq => ⟨hq.1, Set.mem_univ _⟩)
  have hu := (contMDiffOn_diffeomorph_pushforward Phi hPhi x u).comp
    hsnd (fun _ hq => hq.2)
  have hv := (contMDiffOn_diffeomorph_pushforward Phi hPhi x v).comp
    hsnd (fun _ hq => hq.2)
  have hp := ContMDiffOn.clm_bundle_apply₂
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    (F₃ := ℝ) (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
    (E₃ := fun _ : M => ℝ) (b := fun q : ℝ × ℝ => Phi q.2 x)
    (ψ := fun q => (g q.1).inner (Phi q.2 x)) hmetric hu hv
  apply ContMDiffOn.contDiffOn
  intro q hq
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hp q hq)).2

theorem contMDiffOn_pushforward_field {J : Set ℝ} {U : Set M}
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (J ×ˢ Set.univ))
    (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% X) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => (⟨Phi p.1 p.2,
        mfderiv (𝓡 n) (𝓡 n) (Phi p.1) p.2 (X p.2)⟩ :
          TangentBundle (𝓡 n) M)) (J ×ˢ U) := by
  intro p hp
  have hf : ContMDiffWithinAt
      ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : (ℝ × M) × M => Phi q.1.1 q.2)
      ((J ×ˢ U) ×ˢ Set.univ) (p, p.2) :=
    (hPhi (p.1, p.2) ⟨hp.1, Set.mem_univ _⟩).comp (p, p.2)
      (f := fun q : (ℝ × M) × M => (q.1.1, q.2))
      (contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd)
      (fun _ hq => ⟨hq.1.1, hq.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin
    (n := ∞) (m := ∞) (f := fun q : ℝ × M => (Phi q.1 : M → M))
    (g := Prod.snd) hf contMDiffWithinAt_snd hp
    (fun _ _ => Set.mem_univ _) (by simp) uniqueMDiffOn_univ
  have hfield : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : ℝ × M => (⟨q.2, X q.2⟩ : TangentBundle (𝓡 n) M)) (J ×ˢ U) p :=
    (hX p.2 hp.2).comp p (f := Prod.snd) contMDiffWithinAt_snd
      (fun (q : ℝ × M) (hq : q ∈ J ×ˢ U) => hq.2)
  have hbase := (hPhi.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ U))) p hp
  have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := 𝓡 n) (IB₂ := 𝓡 n) (IM := 𝓘(ℝ, ℝ).prod (𝓡 n))
    (b₁ := Prod.snd) (b₂ := fun q : ℝ × M => Phi q.1 q.2) hd hfield hbase
  simpa only [mfderivWithin_univ] using happ

theorem contMDiffOn_pullback_pair {J : Set ℝ} {U : Set M}
    (g : ℝ → RiemannianMetric n M)
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (J ×ˢ Set.univ))
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% Y) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => pinner (g p.1) (Phi p.1) p.2 (X p.2) (Y p.2))
      (J ×ˢ U) := by
  have hbase := hPhi.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ U))
  have hmetric := hg.comp (contMDiffOn_fst.prodMk hbase)
    (fun _ hp => ⟨hp.1, Set.mem_univ _⟩)
  have hp := ContMDiffOn.clm_bundle_apply₂
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    (F₃ := ℝ) (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
    (E₃ := fun _ : M => ℝ) (b := fun p : ℝ × M => Phi p.1 p.2)
    (ψ := fun p => (g p.1).inner (Phi p.1 p.2)) hmetric
    (contMDiffOn_pushforward_field Phi hPhi X hX)
    (contMDiffOn_pushforward_field Phi hPhi Y hY)
  intro p hpU
  have hs := (Bundle.contMDiffWithinAt_totalSpace.mp (hp p hpU)).2
  change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
    (fun q : ℝ × M => (g q.1).inner (Phi q.1 q.2)
      (mfderiv (𝓡 n) (𝓡 n) (Phi q.1) q.2 (X q.2))
      (mfderiv (𝓡 n) (𝓡 n) (Phi q.1) q.2 (Y q.2))) (J ×ˢ U) p at hs
  simpa only [pinner_apply] using hs

theorem contMDiffOn_pullback_section {J : Set ℝ}
    (g : ℝ → RiemannianMetric n M)
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (J ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, pinner (g p.1) (Phi p.1) p.2⟩ :
        Bundle.TotalSpace ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
          (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
          (fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)))
      (J ×ˢ Set.univ) := by
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2
  have he : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
  let F (a : EuclideanSpace ℝ (Fin n)) (y : M) : TangentSpace (𝓡 n) y :=
    e.symmL ℝ y a
  have hF (a : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro y hy
    simpa [F, Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd (e.apply_mk_symm hy a)
  have hsmall : J ×ˢ e.baseSet ∈ 𝓝[J ×ˢ Set.univ] p := by
    have hpre := continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hpre] with q hq hqe
    exact ⟨hq.1, hqe⟩
  apply (contMDiffWithinAt_hom_bundle _).mpr
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  apply Proofs.M03.contMDiffWithinAt_clm_apply_iff.mpr
  intro a
  apply Proofs.M03.contMDiffWithinAt_clm_apply_iff.mpr
  intro b
  have hpair := contMDiffOn_pullback_pair g Phi hg hPhi (F a) (F b) (hF a) (hF b)
  apply ((hpair p ⟨hp.1, he⟩).mono_of_mem_nhdsWithin hsmall).congr_of_eventuallyEq_of_mem _ hp
  filter_upwards [hsmall] with q hq
  rw [inCoordinates_apply_eq₂
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
    (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n)) (E₃ := fun _ : M => ℝ)
    hq.2 hq.2 (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  simp only [F, Trivialization.symmL_apply _ hq.2, e]

theorem contMDiff_pullback_section (g : RiemannianMetric n M)
    (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) :
    ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)) ∞
      (fun x : M => (⟨x, pinner g Phi x⟩ :
        Bundle.TotalSpace ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
          (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
          (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] ℝ))) := by
  have hg : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) Set.univ :=
    (g.contMDiff.comp contMDiff_snd).contMDiffOn
  have hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.2) (Set.univ ×ˢ Set.univ) :=
    (Phi.contMDiff.comp contMDiff_snd).contMDiffOn
  have h := contMDiffOn_pullback_section (fun _ : ℝ => g) (fun _ : ℝ => Phi) hg hPhi
  rw [Set.univ_prod_univ, contMDiffOn_univ] at h
  exact h.comp (contMDiff_const (c := (0 : ℝ)).prodMk contMDiff_id)

def pullbackData {J : Set ℝ} {g0 : RiemannianMetric n M}
    (g : ℝ → RiemannianMetric n M)
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (J ×ˢ Set.univ))
    (hg0 : g 0 = g0) (hPhi0 : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞) :
    PullbackMetricFamilyData J g0 where
  baseMetric := g
  diffeo := Phi
  sliceSmooth := fun t => contMDiff_pullback_section (g t) (Phi t)
  jointSmooth := contMDiffOn_pullback_section g Phi hg hPhi
  baseInitial := hg0
  diffeoInitial := hPhi0



structure DeTurckConjugatingData (g0 : RiemannianMetric n M) where
  T : ℝ
  hT : 0 < T
  pullback : PullbackMetricFamilyData (Set.Ico 0 T) g0
  deTurckSmooth :
    RiemannianMetric.IsSmoothFamilyOn pullback.baseMetric (Set.Ico 0 T)
  deTurckEquation : ∀ t ∈ Set.Ico 0 T, ∀ (x : M)
    (u v : TangentSpace (𝓡 n) x),
    HasDerivWithinAt (fun s => (pullback.baseMetric s).inner x u v)
      (deTurckRHS g0 (pullback.baseMetric t) x u v) (Set.Ico 0 T) t
  conjugatorGenerated : ∀ t ∈ Set.Ico 0 T, ∀ x : M,
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s => pullback.diffeo s x) (Set.Ico 0 T) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-deTurckField g0 (pullback.baseMetric t) (pullback.diffeo t x)))
  jointDerivative : ∀ (t : ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x), (ℝ × ℝ) →L[ℝ] ℝ
  jointFDeriv : ∀ t ∈ Set.Ico 0 T, ∀ (x : M)
    (u v : TangentSpace (𝓡 n) x),
    HasFDerivWithinAt
      (fun q : ℝ × ℝ =>
        (pullback.baseMetric q.1).inner (pullback.diffeo q.2 x)
          (mfderiv (𝓡 n) (𝓡 n) (pullback.diffeo q.2) x u)
          (mfderiv (𝓡 n) (𝓡 n) (pullback.diffeo q.2) x v))
      (jointDerivative t x u v)
      (Set.Ico 0 T ×ˢ Set.Ico 0 T) (t, t)
  gaugeDerivative : ∀ t ∈ Set.Ico 0 T, ∀ (x : M)
    (u v : TangentSpace (𝓡 n) x),
    jointDerivative t x u v (0, 1) = -pulledLie pullback t x u v

namespace DeTurckConjugatingData



def ofFamilies {g0 : RiemannianMetric n M} {T : ℝ} (hT : 0 < T)
    (g : ℝ → RiemannianMetric n M)
    (Phi : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T))
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ))
    (hg0 : g 0 = g0) (hPhi0 : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hpde : ∀ t ∈ Set.Ico 0 T, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (deTurckRHS g0 (g t) x u v) (Set.Ico 0 T) t)
    (hgen : ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => Phi s x) (Set.Ico 0 T) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-deTurckField g0 (g t) (Phi t x)))) :
    DeTurckConjugatingData g0 := by
  let F (x : M) (u v : TangentSpace (𝓡 n) x) (q : ℝ × ℝ) : ℝ :=
    (g q.1).inner (Phi q.2 x)
      (mfderiv (𝓡 n) (𝓡 n) (Phi q.2) x u)
      (mfderiv (𝓡 n) (𝓡 n) (Phi q.2) x v)
  have hF (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
      (u v : TangentSpace (𝓡 n) x) :
      HasFDerivWithinAt (F x u v)
        (fderivWithin ℝ (F x u v) (Set.Ico 0 T ×ˢ Set.Ico 0 T) (t, t))
        (Set.Ico 0 T ×ˢ Set.Ico 0 T) (t, t) :=
    ((contDiffOn_twoTimeEvaluation g Phi hg hPhi x u v).differentiableOn
      (by simp) (t, t) ⟨ht, ht⟩).hasFDerivWithinAt
  refine {
    T := T
    hT := hT
    pullback := pullbackData g Phi hg hPhi hg0 hPhi0
    deTurckSmooth := hg
    deTurckEquation := hpde
    conjugatorGenerated := hgen
    jointDerivative := fun t x u v =>
      fderivWithin ℝ (F x u v) (Set.Ico 0 T ×ˢ Set.Ico 0 T) (t, t)
    jointFDeriv := hF
    gaugeDerivative := ?_ }
  intro t ht x u v
  have hslice : HasDerivWithinAt (fun s : ℝ => (t, s)) (0, 1)
      (Set.Ico 0 T) t := by
    simpa using (hasDerivWithinAt_const t (Set.Ico 0 T) t).prodMk
      (hasDerivWithinAt_id t (Set.Ico 0 T))
  have hmaps : Set.MapsTo (fun s : ℝ => (t, s))
      (Set.Ico 0 T) (Set.Ico 0 T ×ˢ Set.Ico 0 T) := fun _ hs => ⟨ht, hs⟩
  have hpartial := HasFDerivWithinAt.comp_hasDerivWithinAt t
    (f := fun s : ℝ => (t, s)) (hF t ht x u v) hslice hmaps
  have htransport := ConjugatorLieDerivativeNative.hasDerivWithinAt_fixedMetric_pullback_neg
    hT ht (connection (g t)) Phi (deTurckField g0 (g t)) hPhi
    (DeTurckNative.intrinsicDeTurckField_contMDiffAt (connection (g t)) (connection g0))
    (hgen t ht) x u v
  exact (uniqueDiffOn_Ico 0 T t ht).eq_deriv _ hpartial htransport

variable {g0 : RiemannianMetric n M} (A : DeTurckConjugatingData g0)

theorem metricTimeDerivative (t : ℝ) (ht : t ∈ Set.Ico 0 A.T)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    A.jointDerivative t x u v (1, 0) = pulledSource A.pullback t x u v := by
  have hslice : HasDerivWithinAt (fun s : ℝ => (s, t)) (1, 0)
      (Set.Ico 0 A.T) t := by
    simpa using (hasDerivWithinAt_id t (Set.Ico 0 A.T)).prodMk
      (hasDerivWithinAt_const t (Set.Ico 0 A.T) t)
  have hmaps : Set.MapsTo (fun s : ℝ => (s, t))
      (Set.Ico 0 A.T) (Set.Ico 0 A.T ×ˢ Set.Ico 0 A.T) :=
    fun _ hs => ⟨hs, ht⟩
  have hpartial := HasFDerivWithinAt.comp_hasDerivWithinAt t
    (f := fun s : ℝ => (s, t)) (A.jointFDeriv t ht x u v) hslice hmaps
  have hpde := A.deTurckEquation t ht (A.pullback.diffeo t x)
    (mfderiv (𝓡 n) (𝓡 n) (A.pullback.diffeo t) x u)
    (mfderiv (𝓡 n) (𝓡 n) (A.pullback.diffeo t) x v)
  exact (uniqueDiffOn_Ico 0 A.T t ht).eq_deriv _ hpartial hpde

theorem diagonalDerivative (t : ℝ) (ht : t ∈ Set.Ico 0 A.T)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    A.jointDerivative t x u v (1, 1) =
      pulledSource A.pullback t x u v - pulledLie A.pullback t x u v := by
  have hsplit : ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) := by ext <;> simp
  rw [hsplit, map_add, A.metricTimeDerivative t ht x u v,
    A.gaugeDerivative t ht x u v, sub_eq_add_neg]

theorem transportedEquation (t : ℝ) (ht : t ∈ Set.Ico 0 A.T)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (A.pullback.metric s).inner x u v)
      (pulledSource A.pullback t x u v - pulledLie A.pullback t x u v)
      (Set.Ico 0 A.T) t := by
  have h := hasDerivWithinAt_pullbackMetric_of_jointFDeriv
    A.pullback.baseMetric A.pullback.diffeo A.pullback.sliceSmooth
    (A.jointFDeriv t ht x u v)
  exact h.congr_deriv (A.diagonalDerivative t ht x u v)

theorem source_continuous (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContinuousOn
      (fun t => pulledSource A.pullback t x u v - pulledLie A.pullback t x u v)
      (Set.Ico 0 A.T) := by
  have hsm := contDiffOn_metric_evaluation A.pullback.metric_isSmoothFamilyOn x u v
  have hcont := hsm.continuousOn_derivWithin (uniqueDiffOn_Ico 0 A.T) (by simp)
  apply hcont.congr
  intro t ht
  exact ((A.transportedEquation t ht x u v).derivWithin
    (uniqueDiffOn_Ico 0 A.T t ht)).symm

theorem integral_equation (t : ℝ) (ht : t ∈ Set.Ico 0 A.T)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    (A.pullback.metric t).inner x u v = g0.inner x u v +
      ∫ s in (0 : ℝ)..t,
        pulledSource A.pullback s x u v - pulledLie A.pullback s x u v := by
  exact IntegralGaugeFTCNative.metric_inner_eq_add_integral_Ico
    A.pullback.metric_initial A.source_continuous A.transportedEquation t ht x u v

theorem source_sub_gauge (t : ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    pulledSource A.pullback t x u v - pulledLie A.pullback t x u v =
      -2 * (connection (A.pullback.baseMetric t)).ricci (A.pullback.diffeo t x)
        (mfderiv (𝓡 n) (𝓡 n) (A.pullback.diffeo t) x u)
        (mfderiv (𝓡 n) (𝓡 n) (A.pullback.diffeo t) x v) := by
  exact add_sub_cancel_right _ _

theorem cancellation (t : ℝ) (P : LeviCivitaData (A.pullback.metric t))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    pulledSource A.pullback t x u v - pulledLie A.pullback t x u v =
      -2 * P.ricci x u v := by
  classical
  let D := connection (A.pullback.baseMetric t)
  let e := (A.pullback.diffeo t).mfderivToContinuousLinearEquiv (by simp) x
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let b := Module.finBasis ℝ (TangentSpace (𝓡 n) x)
  have hRicci : P.ricci x u v = D.ricci (A.pullback.diffeo t x) (e u) (e v) := by
    rw [Proofs.M03.ricci_eq_sum_basis P x u v b,
      Proofs.M03.ricci_eq_sum_basis D _ (e u) (e v) (b.map e.toLinearEquiv)]
    apply Finset.sum_congr rfl
    intro i _
    have hcurv := DiffeomorphNative.curvature_pullback
      (A.pullback.baseMetric t) (A.pullback.diffeo t) (A.pullback.sliceSmooth t)
      D P x (b i) u v
    change e (P.curvature x (b i) u v) =
      D.curvature (A.pullback.diffeo t x) (e (b i)) (e u) (e v) at hcurv
    change b.repr (P.curvature x (b i) u v) i =
      (b.map e.toLinearEquiv).repr
        (D.curvature (A.pullback.diffeo t x) (e (b i)) (e u) (e v)) i
    rw [← hcurv]
    simp
  rw [A.source_sub_gauge]
  exact congrArg (fun r : ℝ => -2 * r) hRicci.symm

def certificate : GaugeRecovery.Certificate g0 where
  T := A.T
  hT := A.hT
  metric := A.pullback.metric
  connection := fun t => connection (A.pullback.metric t)
  smooth := A.pullback.metric_isSmoothFamilyOn
  initial := A.pullback.metric_initial
  source := pulledSource A.pullback
  gaugeCorrection := pulledLie A.pullback
  transportedEquation := A.transportedEquation
  cancellation := fun t _ P x u v => A.cancellation t P x u v

def integralCertificate : IntegralGaugeRecovery.Certificate g0 :=
  A.certificate.toIntegral A.source_continuous

include A in
theorem exists_metricFamily :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ t ∈ Set.Ico 0 T, ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s => (g s).inner x u v)
          (-2 * D.ricci x u v) (Set.Ico 0 T) t :=
  IntegralGaugeRecovery.exists_metricFamily A.integralCertificate

end DeTurckConjugatingData

end PoincareConjecture.MetricFamilyProducerNative

end
