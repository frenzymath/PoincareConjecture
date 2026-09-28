import PoincareConjecture.Proofs.M35.Thm12_28.SelectedNeckJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)

private theorem fixed_coordinate_metric_sum
    {M N : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace V N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (F : M → N) (f : V → M) (q : M) (p v w : V)
    (hp : f p ∈ (extChartAt (𝓡 3) q).source)
    (hF : ContMDiffAt (𝓡 3) (𝓡 3) ∞ F (f p))
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f p) :
    g.pullbackCoefficients (F ∘ f) p v w =
      ∑ a : Fin 3, ∑ b : Fin 3,
        g.pullbackCoefficients (F ∘ (extChartAt (𝓡 3) q).symm) (extChartAt (𝓡 3) q (f p))
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) *
        (fderiv ℝ (extChartAt (𝓡 3) q ∘ f) p v) a *
        (fderiv ℝ (extChartAt (𝓡 3) q ∘ f) p w) b := by
  have hFd := mfderiv_comp p (hF.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  have hFv (z : V) : mfderiv (𝓡 3) (𝓡 3) (F ∘ f) p z =
      mfderiv (𝓡 3) (𝓡 3) F (f p) (mfderiv (𝓡 3) (𝓡 3) f p z) :=
    congrArg (fun A : V →L[ℝ] V => A z) hFd
  let c := extChartAt (𝓡 3) q
  have hsource : f p ∈ (chartAt V q).source := by
    rwa [← extChartAt_source (I := 𝓡 3)]
  have hc := contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hsource
  have hd := mfderiv_comp p (hc.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hmetric := g.pullbackCoefficients_chart_cancel F q hp hF
    (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w)
  let A := g.pullbackCoefficients (F ∘ c.symm) (c (f p))
  let u := fderiv ℝ (c ∘ f) p v
  let z := fderiv ℝ (c ∘ f) p w
  have hv : mfderiv (𝓡 3) (𝓡 3) c (f p)
      (mfderiv (𝓡 3) (𝓡 3) f p v) = u :=
    (congrArg (fun B : V →L[ℝ] V => B v) hd).symm
  have hw : mfderiv (𝓡 3) (𝓡 3) c (f p)
      (mfderiv (𝓡 3) (𝓡 3) f p w) = z :=
    (congrArg (fun B : V →L[ℝ] V => B w) hd).symm
  rw [hv, hw] at hmetric
  refine (congrArg₂ (fun a b : V => g.inner (F (f p)) a b) (hFv v) (hFv w)).trans
    (hmetric.symm.trans ?_)
  have he (y : V) : ∑ a : Fin 3, y a • EuclideanSpace.basisFun (Fin 3) ℝ a = y := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y
  change A u z = ∑ a : Fin 3, ∑ b : Fin 3,
    A (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) * u a * z b
  calc
    A u z = A (∑ a : Fin 3, u a • EuclideanSpace.basisFun (Fin 3) ℝ a)
      (∑ b : Fin 3, z b • EuclideanSpace.basisFun (Fin 3) ℝ b) := by rw [he, he]
    _ = _ := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

private theorem fixed_coordinate_error_jets
    (psi : V → V) (pseq : ℕ → V) (p v w : V)
    (A : ℕ → V → Fin 3 → Fin 3 → ℝ) (r : ℕ)
    (hp : Tendsto pseq atTop (𝓝 p))
    (hs : ContDiffAt ℝ ∞ psi p) (hseq : ∀ k, ContDiffAt ℝ ∞ psi (pseq k))
    (hA : ∀ a b : Fin 3, ∀ᶠ k in atTop,
      ContDiffAt ℝ ∞ (fun y => A k y a b) (psi (pseq k)))
    (hjet : ∀ m ≤ r, ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k y a b) (psi (pseq k)))
        atTop (𝓝 0)) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y : V =>
      ∑ a : Fin 3, ∑ b : Fin 3,
        A k (psi y) a b * (fderiv ℝ psi y v) a * (fderiv ℝ psi y w) b) (pseq k))
      atTop (𝓝 0) := by
  let W (u : V) (a : Fin 3) (y : V) := (fderiv ℝ psi y u) a
  have hW {y : V} (hy : ContDiffAt ℝ ∞ psi y) (u : V) (a : Fin 3) :
      ContDiffAt ℝ ∞ (W u a) y := by
    have hd : ContDiffAt ℝ ∞ (fun z => fderiv ℝ psi z u) y :=
      (hy.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    exact (EuclideanSpace.proj a).contDiff.contDiffAt.comp y hd
  have hWlim (m : ℕ) (u : V) (a : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ m (W u a) (pseq k)) atTop
        (𝓝 (iteratedFDeriv ℝ m (W u a) p)) :=
    ((hW hs u a).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hp
  have hpsi (m : ℕ) : Tendsto (fun k => iteratedFDeriv ℝ m psi (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m psi p)) :=
    (hs.continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hp
  let H (k : ℕ) (a b : Fin 3) (y : V) := A k (psi y) a b * W v a y * W w b y
  have hH (a b : Fin 3) : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (H k a b) (pseq k) :=
    (hA a b).mono fun k hk => ((hk.comp (pseq k) (hseq k)).mul
      (hW (hseq k) v a)).mul (hW (hseq k) w b)
  have hlim (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r (H k a b) (pseq k)) atTop (𝓝 0) := by
    have hcomp (m : ℕ) (hm : m ≤ r) :
        Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k (psi y) a b) (pseq k))
          atTop (𝓝 0) := by
      have h := tendsto_iteratedFDeriv_comp_of_jets m hs
        (contDiffAt_const (c := (0 : ℝ))) (Eventually.of_forall hseq) (hA a b)
        (fun n _ => hpsi n) (fun n hn => by
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hjet n (hn.trans hm) a b)
      simpa only [Function.comp_def, iteratedFDeriv_fun_zero, Pi.zero_apply] using h
    have hfirst (m : ℕ) (hm : m ≤ r) :
        Tendsto (fun k => iteratedFDeriv ℝ m
          (fun y => A k (psi y) a b * W v a y) (pseq k)) atTop (𝓝 0) := by
      have h := tendsto_iteratedFDeriv_mul_of_jets
        (f₀ := fun _ => (0 : ℝ)) (g₀ := W v a) m contDiffAt_const (hW hs v a)
        ((hA a b).mono fun k hk => hk.comp (pseq k) (hseq k))
        (Eventually.of_forall fun k => hW (hseq k) v a)
        (fun n hn => by
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using
            hcomp n (hn.trans hm))
        (fun n _ => hWlim n v a)
      simpa only [zero_mul, iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using h
    have h := tendsto_iteratedFDeriv_mul_of_jets
      (f₀ := fun _ => (0 : ℝ)) (g₀ := W w b) r contDiffAt_const (hW hs w b)
      ((hA a b).mono fun k hk => (hk.comp (pseq k) (hseq k)).mul (hW (hseq k) v a))
      (Eventually.of_forall fun k => hW (hseq k) w b)
      (fun m hm => by
        simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using hfirst m hm)
      (fun m _ => hWlim m w b)
    simpa only [H, zero_mul, iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using h
  have hsum := tendsto_finsetSum Finset.univ (fun a _ =>
    tendsto_finsetSum Finset.univ (fun b _ => hlim a b))
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr'
  have hAll : ∀ᶠ k in atTop, ∀ a b : Fin 3, ContDiffAt ℝ ∞ (H k a b) (pseq k) :=
    eventually_all.mpr fun a => eventually_all.mpr fun b => hH a b
  filter_upwards [hAll] with k hk
  symm
  change iteratedFDeriv ℝ r (fun y => ∑ a : Fin 3, ∑ b : Fin 3, H k a b y) (pseq k) = _
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  rw [iteratedFDeriv_fun_sum_apply (fun a _ =>
    (ContDiffAt.sum (fun b _ => hk a b)).of_le hr)]
  exact Finset.sum_congr rfl (fun a _ =>
    iteratedFDeriv_fun_sum_apply (fun b _ => (hk a b).of_le hr))

namespace OrdinaryRealization



theorem blowupSequence_fixed_coordinate_error_jets
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (pseq : ℕ → V) (p : V) (_hp : Tendsto pseq atTop (𝓝 p))
      (c : L.limit.sliceCarrier.carrier)
      (_hc₀ : coordinate p ∈ (extChartAt (𝓡 3) c).source)
      (_hcseq : ∀ k, coordinate (pseq k) ∈ (extChartAt (𝓡 3) c).source)
      (j : ℕ) (K : Set (ℝ × V)) (_hK : IsCompact K)
      (_hKU : K ⊆ {p | p ∈ blowupMetricChartDomain L.limit c ∧
        (extChartAt (𝓡 3) c).symm p.2 ∈ L.exhaustion.space j})
      (sigma : ℕ → ℕ) (_hsigma : Tendsto sigma atTop atTop)
      (_hpoints : ∀ k, (0, extChartAt (𝓡 3) c (coordinate (pseq k))) ∈ K)
      (r : ℕ) (v w : V),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding (sigma k)).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y : V =>
        Q k * (E.flow.metric (t (L.subsequence (sigma k)))).pullbackCoefficients
          (F k ∘ coordinate) y v w -
        (L.limit.flow.metric 0).pullbackCoefficients coordinate y v w) (pseq k))
          atTop (𝓝 0) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate hcoord pseq p hp c hc₀ hcseq j K hK hKU sigma hsigma hpoints r v w
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    ((L.embedding (sigma k)).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
  let psi : V → V := extChartAt (𝓡 3) c ∘ coordinate
  let A (k : ℕ) (y : V) (i j : Fin 3) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence (sigma k))) (Q k) (F k) c i j (0, y) -
    FlowCarrier.coordinateCoefficient L.limit.carrier c
      (fun s z v w => (L.limit.flow.metric s).inner z v w) i j (0, y)
  have hpsi {y : V} (hy : coordinate y ∈ (extChartAt (𝓡 3) c).source) :
      ContDiffAt ℝ ∞ psi y := by
    have hchart : coordinate y ∈ (chartAt V c).source := by
      rwa [← extChartAt_source (I := 𝓡 3)]
    exact ((contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hchart).comp y (hcoord y)).contDiffAt
  have hcontrol (i j' : Fin 3) :
      (∀ᶠ k in atTop, ContDiffAt ℝ ∞ (fun y => A k y i j') (psi (pseq k))) ∧
      ∀ m : ℕ, Tendsto
        (fun k => iteratedFDeriv ℝ m (fun y => A k y i j') (psi (pseq k))) atTop (𝓝 0) :=
    blowupSequence_spatial_error_jets P E t x ht hR L c j i j' K hK hKU sigma hsigma
      (fun k => (0, psi (pseq k))) hpoints
  have hlim := fixed_coordinate_error_jets psi pseq p v w A r hp (hpsi hc₀)
    (fun k => hpsi (hcseq k)) (fun i j' => (hcontrol i j').1)
    (fun m _ i j' => (hcontrol i j').2 m)
  apply hlim.congr'
  filter_upwards [hsigma.eventually (eventually_ge_atTop j)] with k hk
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time (sigma k)) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
  have htime : t (L.subsequence (sigma k)) + 0 / Q k ∈ Ico 0 E.flow.base.lifetime :=
    ((L.embedding (sigma k)).forward 0 hzero L.limit.base).property
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (F k) (L.exhaustion.space (sigma k)) :=
    (sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
      ((L.embedding (sigma k)).forward_smooth 0 hzero)
  have hyj : coordinate (pseq k) ∈ L.exhaustion.space j := by
    have hy := (hKU (hpoints k)).2
    rwa [(extChartAt (𝓡 3) c).left_inv (hcseq k)] at hy
  have hnearC := (hcoord (pseq k)).continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 3) c).mem_nhds (hcseq k))
  have hnearF := (hcoord (pseq k)).continuousAt.preimage_mem_nhds
    ((L.exhaustion.space_open (sigma k)).mem_nhds
      (L.exhaustion.space_increasing hk hyj))
  have hgerm : (fun y : V =>
      Q k * (E.flow.metric (t (L.subsequence (sigma k)))).pullbackCoefficients
        (F k ∘ coordinate) y v w -
      (L.limit.flow.metric 0).pullbackCoefficients coordinate y v w) =ᶠ[𝓝 (pseq k)]
      (fun y => ∑ i : Fin 3, ∑ j' : Fin 3, A k (psi y) i j' *
        (fderiv ℝ psi y v) i * (fderiv ℝ psi y w) j') := by
    filter_upwards [hnearC, hnearF] with y hyC hyF
    have hfo := hF.contMDiffAt ((L.exhaustion.space_open (sigma k)).mem_nhds hyF)
    have hfirst := fixed_coordinate_metric_sum
      (E.flow.metric (t (L.subsequence (sigma k)))) (F k) coordinate c y v w hyC hfo (hcoord y)
    have hsecond := fixed_coordinate_metric_sum
      (L.limit.flow.metric 0) id coordinate c y v w hyC contMDiffAt_id (hcoord y)
    have hcoef (i j' : Fin 3) : A k (psi y) i j' =
        Q k * (E.flow.metric (t (L.subsequence (sigma k)))).pullbackCoefficients
          (F k ∘ (extChartAt (𝓡 3) c).symm) (psi y)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j') -
        (L.limit.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) c).symm (psi y)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j') := by
      have hinv : (extChartAt (𝓡 3) c).symm (psi y) = coordinate y :=
        (extChartAt (𝓡 3) c).left_inv hyC
      have hfixed := fixedCylinderMetricCoefficient_eq_pullback E.flow.base.flow
        L.limit.sliceCarrier (t (L.subsequence (sigma k))) (Q k) (F k) c i j'
        (0, psi y) ((extChartAt (𝓡 3) c).map_source hyC) (hinv.symm ▸ hfo)
      simp only [zero_div, add_zero] at hfixed
      exact congrArg (fun z : ℝ => z -
        (L.limit.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) c).symm (psi y)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j')) hfixed
    refine (congrArg₂ (fun a b : ℝ => Q k * a - b) hfirst hsecond).trans ?_
    simp_rw [hcoef]
    simp only [Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      psi, Function.comp_def, id_eq]
  exact ((hgerm.iteratedFDeriv ℝ r).self_of_nhds).symm

end OrdinaryRealization

end PoincareConjecture.M35
