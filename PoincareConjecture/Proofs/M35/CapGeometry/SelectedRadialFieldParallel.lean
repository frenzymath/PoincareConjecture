import PoincareConjecture.Proofs.M35.CapGeometry.SelectedRadialFieldExtraction
import PoincareConjecture.Proofs.M35.CapGeometry.RadialFieldLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

noncomputable section

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ

local instance selectedParallelDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance selectedParallelDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance selectedParallelMetricNormedGroup : NormedAddCommGroup B := inferInstance
local instance selectedParallelMetricNormedSpace : NormedSpace ℝ B := inferInstance

theorem blowupSequence_coordinate_radial_limit_parallel
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (_hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
      (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
      (_hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients coordinate)
      (sigma : ℕ → ℕ) (_hsigma : Tendsto sigma atTop atTop)
      (p : V) (Z : V → V) (_hZ : ContDiffAt ℝ ∞ Z p),
      (∀ m ≤ 1, Tendsto (fun k => iteratedFDeriv ℝ m
        (selectedCoordinateRadialField P E t x ht hR L coordinate (sigma k)) p) atTop
          (𝓝 (iteratedFDeriv ℝ m Z p))) →
      g.inner p (Z p) (Z p) = 1 ∧ ∀ w : V, D.connection Z p w = 0 := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.sliceCarrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.sliceCarrier.carrier := L.limit.connectedSpace
  intro coordinate hc hi g D hg sigma hsigma p Z hZ hjet
  have hdomain := hsigma.eventually
    (blowupSequence_coordinate_radial_domain P E t x ht hR hd L
      coordinate hc hi {p} isCompact_singleton)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdomain
  let mu (k : ℕ) := k + N
  have hmu : StrictMono mu := fun i j hij => Nat.add_lt_add_right hij N
  let idx := sigma ∘ mu
  have hidx : Tendsto idx atTop atTop := hsigma.comp hmu.tendsto_atTop
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (idx k))
  have hQ k : 0 < Q k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence (idx k))
  let G (k : ℕ) : RiemannianMetric 3 V :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence (idx k)))) (Q k) (hQ k)
  let DG (k : ℕ) : LeviCivitaData (G k) :=
    M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence (idx k)))) (Q k) (hQ k)
  let f (k : ℕ) (z : V) := ((L.embedding (idx k)).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos (idx k)).le, le_rfl⟩ (coordinate z)).val
  let Zseq k := pullback ℝ (f k) (radialUnitField (G k))
  have hgood (k : ℕ) : ∀ᶠ y in 𝓝 p, ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f k) y ∧
      (mfderiv (𝓡 3) (𝓡 3) (f k) y).IsInvertible ∧ f k y ≠ 0 :=
    (hN (mu k) (Nat.le_add_left N k) p (mem_singleton _)).1
  have hreal (k : ℕ) : ∃ gd : Σ g' : RiemannianMetric 3 V, LeviCivitaData g',
      gd.1.euclideanCoefficients =ᶠ[𝓝 p] (G k).pullbackCoefficients (f k) := by
    obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp (hgood k)
    obtain ⟨gk, Dk, hcoeff, _⟩ := exists_local_curvature_derivative_realization
      (G k) (DG k) (f k) hU hpU
      (fun y hy => (hUsub hy).1) (fun y hy => (hUsub hy).2.1)
    exact ⟨⟨gk, Dk⟩, hcoeff⟩
  choose gd hgd using hreal
  have hmetric (k : ℕ) : ∀ᶠ y in 𝓝 p, ∀ u v : V,
      (gd k).1.inner y u v = (G k).inner (f k y)
        (mfderiv (𝓡 3) (𝓡 3) (f k) y u) (mfderiv (𝓡 3) (𝓡 3) (f k) y v) := by
    filter_upwards [hgd k] with y hy u v
    exact congrArg (fun b : B => b u v) hy
  have hmjets (r : ℕ) : Tendsto (fun k => iteratedFDeriv ℝ r (gd k).1.euclideanCoefficients p)
      atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p)) :=
    blowupSequence_fixed_coordinate_metric_jets P E t x ht hR L coordinate hc
      (fun _ => p) p tendsto_const_nhds idx hidx (fun k => (gd k).1) g
      (Eventually.of_forall hgd) (Eventually.of_forall fun y => congrFun hg y) r
  have hrotation (k : ℕ) : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V, (G k).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G k).inner x u v :=
    scaleSmoothMetric_rotation_invariant (E.rotation_invariant (t (L.subsequence (idx k)))
      (ht _)) _ _
  let glim : RiemannianMetric 3 L.limit.sliceCarrier.carrier := L.limit.flow.metric 0
  let R := (glim.edist L.limit.base (coordinate p)).toReal + 1
  have hpball : coordinate p ∈ glim.ball L.limit.base R :=
    (ENNReal.lt_ofReal_iff_toReal_lt (glim.edist_ne_top _ _)).mpr
      (lt_add_of_pos_right _ zero_lt_one)
  have hbound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ w : V,
      (G k).inner (f k p) ((DG k).connection (radialUnitField (G k)) (f k p) w)
        ((DG k).connection (radialUnitField (G k)) (f k p) w) ≤
          ε ^ 2 * (G k).inner (f k p) w w := by
    have hh := hidx.eventually
      (blowupSequence_far_tip_radial_field_on_limit_ball P E t x ht hR hd L R ε hε)
    filter_upwards [hh] with k hk
    exact (hk (coordinate p) hpball).2.2
  have hs (k : ℕ) : ContDiffAt ℝ ∞ (Zseq k) p := by
    have hf := contMDiffAt_iff_contDiffAt.mp (hgood k).self_of_nhds.1
    have hi' : (fderiv ℝ (f k) p).IsInvertible := by
      simpa only [mfderiv_eq_fderiv] using (hgood k).self_of_nhds.2.1
    exact euclidean_radial_pullback_contDiffAt _ hf hi' (hgood k).self_of_nhds.2.2
  have hretain (k : ℕ) (ε : ℝ)
      (hb : ∀ w : V, (G k).inner (f k p)
        ((DG k).connection (radialUnitField (G k)) (f k p) w)
        ((DG k).connection (radialUnitField (G k)) (f k p) w) ≤
          ε ^ 2 * (G k).inner (f k p) w w) :
      (gd k).1.inner p (Zseq k p) (Zseq k p) = 1 ∧ ∀ w : V,
        (gd k).1.inner p ((gd k).2.connection (Zseq k) p w)
          ((gd k).2.connection (Zseq k) p w) ≤ ε ^ 2 * (gd k).1.inner p w w := by
    have hh := radialUnitField_pullback (gd k).2 (DG k) (hrotation k)
      (hgood k).self_of_nhds.1 ((hgood k).mono fun _ hy => hy.2.1)
      (hmetric k) (hgood k).self_of_nhds.2.2 ε hb
    simpa only [Zseq, mpullback_eq_pullback] using! hh.2
  exact parallel_unit_of_metric_and_field_jets (fun k => (gd k).2) D
    (fun _ => p) p hZ hs (fun r _ => hmjets r)
    (fun r hr => (hjet r hr).comp hmu.tendsto_atTop)
    ((hbound 1 zero_lt_one).mono fun k hk => (hretain k 1 hk).1)
    (fun ε hε => (hbound ε hε).mono fun k hk => (hretain k ε hk).2)

end

end PoincareConjecture.M35.OrdinaryRealization
