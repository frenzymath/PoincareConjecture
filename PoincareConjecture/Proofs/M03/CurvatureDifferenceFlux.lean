import PoincareConjecture.Proofs.M03.CurvatureHessianDivergence

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option synthInstance.maxHeartbeats 200000

private def rawCurvatureAction {n : ℕ}
    (gamma : Fin n → Fin n → Fin n → ℝ) (d : Fin n) :
    (Fin n → Fin n → Fin n → Fin n → ℝ) →ₗ[ℝ]
      Fin n → Fin n → Fin n → Fin n → ℝ where
  toFun T l j k m := ∑ p : Fin n, (
    gamma d p l * T p j k m - gamma d j p * T l p k m -
      gamma d k p * T l j p m - gamma d m p * T l j k p)
  map_add' T U := by
    ext l j k m
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_smul' r T := by
    ext l j k m
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

private def rawDivergenceAction {n : ℕ}
    (gamma : Fin n → Fin n → Fin n → ℝ) :
    (Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) →ₗ[ℝ]
      Fin n → Fin n → Fin n → Fin n → ℝ where
  toFun T l j k m := ∑ i : Fin n, (
    rawCurvatureAction gamma i (T i) l j k m +
      ∑ p : Fin n, gamma i p i * T p l j k m)
  map_add' T U := by
    ext l j k m
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r T := by
    ext l j k m
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul,
      mul_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring

private def rawCurvatureContraction {n dS : ℕ}
    (theta : Fin dS → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (Fin n → Fin n → Fin n → Fin n → ℝ) →ₗ[ℝ] Fin dS → ℝ where
  toFun T alpha := ∑ l, ∑ j, ∑ k, ∑ m, theta alpha l j k m * T l j k m
  map_add' T U := by
    ext alpha
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r T := by
    ext alpha
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    ring

set_option maxHeartbeats 2000000 in

theorem exists_curvature_difference_flux_coordinate_bound
    {n dH dA dS : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let FH := V →L[ℝ] V →L[ℝ] ℝ
    let FA := V →L[ℝ] V →L[ℝ] V
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let BA := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
    ∀ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qA : FA ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (s : Finset M) (Q : M → Set V),
      (∀ a ∈ s, IsCompact (Q a) ∧ Q a ⊆ (chartAt V a).target) →
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J')
        (R R' : (t : ℝ) → (x : M) → BS x),
        (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
        (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
        ∀ (K : Set ℝ), IsCompact K → K ⊆ J ∩ J' →
          let c := chartAt V
          let eT := trivializationAt V (TangentSpace (𝓡 n))
          let eH := trivializationAt FH BH
          let eA := trivializationAt FA BA
          let eS := trivializationAt FS BS
          let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
          let frame := fun a i x => (eT a).symmL ℝ x (e i)
          let G := fun (g : ℝ → RiemannianMetric n M) a (p : ℝ × V) =>
            ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
              ((g p.1).inner ((c a).symm p.2)))).2
          let ai := fun g a p i d => ((G g a p).inverse (EuclideanSpace.proj d)) i
          let gamma := fun g (D : (t : ℝ) → LeviCivitaData (g t)) a (p : ℝ × V) i j l =>
            ((eT a).continuousLinearMapAt ℝ ((c a).symm p.2)
              ((D p.1).connection (frame a j) ((c a).symm p.2)
                (frame a i ((c a).symm p.2)))) l
          let Hbar := fun a (p : ℝ × V) => ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
            ((F.metric p.1).inner ((c a).symm p.2) -
              (F'.metric p.1).inner ((c a).symm p.2)))).2
          let Abar := fun a (p : ℝ × V) => ((eA a) (TotalSpace.mk' FA ((c a).symm p.2)
            (CovariantDerivative.difference (F.connection p.1).connection
              (F'.connection p.1).connection ((c a).symm p.2)))).2
          let Sbar := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
            (R p.1 ((c a).symm p.2) - R' p.1 ((c a).symm p.2)))).2
          let Rbar' := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
            (R' p.1 ((c a).symm p.2)))).2
          let raw := fun (T : FS) l j k m => (EuclideanSpace.proj l) (T (e j) (e k) (e m))
          let ag := fun (A : FA) i j l => (EuclideanSpace.proj l) (A (e j) (e i))
          let act := fun (g : Fin n → Fin n → Fin n → ℝ)
            (T : Fin n → Fin n → Fin n → Fin n → ℝ) d l j k m =>
              ∑ p : Fin n, (g d p l * T p j k m - g d j p * T l p k m -
                g d k p * T l j p m - g d m p * T l j k p)
          let div := fun (g : Fin n → Fin n → Fin n → ℝ)
            (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) l j k m =>
              ∑ i : Fin n, (act g (T i) i l j k m + ∑ p, g i p i * T p l j k m)
          let kp := fun a (p : ℝ × V) d l j k m =>
            fderiv ℝ (fun z => raw (Rbar' a (p.1, z)) l j k m) p.2 (e d) +
              act (gamma F'.metric F'.connection a p) (raw (Rbar' a p)) d l j k m
          let vp := fun a p i l j k m => ∑ d, ai F'.metric a p i d * kp a p d l j k m
          let w := fun a p i l j k m => ∑ d : Fin n,
            (ai F.metric a p i d * act (gamma F.metric F.connection a p)
                (raw (Sbar a p)) d l j k m +
              -((G F.metric a p).inverse
                (Hbar a p ((G F'.metric a p).inverse (EuclideanSpace.proj d)))) i *
                  kp a p d l j k m +
              ai F.metric a p i d * act (ag (Abar a p)) (raw (Rbar' a p)) d l j k m)
          let fH := fun a i p => qH (Hbar a p) i
          let fA := fun a i p => qA (Abar a p) i
          let fS := fun a i p => qS (Sbar a p) i
          let principal := fun a (p : ℝ × V) i l j k m =>
            ∑ d, ai F.metric a p i d * ∑ β : Fin dS,
              raw (qS.symm (EuclideanSpace.single β 1)) l j k m *
                fderiv ℝ (fun z => fS a β (p.1, z)) p.2 (e d)
          let B := fun l j k m : Fin n => (EuclideanSpace.proj j).smulRight
            ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight (e l)))
          let contract := fun (T : Fin n → Fin n → Fin n → Fin n → ℝ) α =>
            ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α * T l j k m
          let U := fun a p α i => contract (w a p i) α
          let W := fun a p α => contract
            (div (gamma F.metric F.connection a p) (principal a p + w a p) +
              div (ag (Abar a p)) (vp a p)) α
          let density := fun a p => (∑ i : Fin dH, (fH a i p) ^ 2) +
            (∑ i : Fin dA, (fA a i p) ^ 2) + (∑ i : Fin dS, (fS a i p) ^ 2)
          let gradient := fun a (p : ℝ × V) => ∑ β : Fin dS, ∑ d : Fin n,
            (fderiv ℝ (fun z => fS a β (p.1, z)) p.2 (e d)) ^ 2
          ∃ CU CR : ℝ, 0 ≤ CU ∧ 0 ≤ CR ∧ ∀ a ∈ s, ∀ t ∈ K, ∀ z ∈ Q a,
            (∑ α : Fin dS, ∑ i : Fin n, (U a (t, z) α i) ^ 2) ≤ CU * density a (t, z) ∧
            ∀ ε : ℝ, 0 < ε → (∑ α : Fin dS, 2 * fS a α (t, z) * W a (t, z) α) ≤
              ε * gradient a (t, z) + (CR / ε + CR) * density a (t, z) := by
  classical
  intro V FH FA FS BH BA BS qH qA qS s Q hQ J J' F F' R R' hR hR' K hK hKJ
  let : NormedAddCommGroup V := by dsimp only [V]; infer_instance
  let : NormedSpace ℝ V := by dsimp only [V]; infer_instance
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup FH := by dsimp only [FH]; infer_instance
  let : NormedSpace ℝ FH := by dsimp only [FH]; infer_instance
  let : NormedAddCommGroup FA := by dsimp only [FA]; infer_instance
  let : NormedSpace ℝ FA := by dsimp only [FA]; infer_instance
  let : NormedAddCommGroup FS := by dsimp only [FS]; infer_instance
  let : NormedSpace ℝ FS := by dsimp only [FS]; infer_instance
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  intro c eT eH eA eS e frame G ai gamma Hbar Abar Sbar Rbar' raw ag act div kp vp w
    fH fA fS principal B contract U W density gradient
  let Raw := Fin n → Fin n → Fin n → Fin n → ℝ
  let Flux := Fin n → Raw
  let contraction := rawCurvatureContraction (fun α l j k m => qS (B l j k m) α)
  let lH (a : M) (p : ℝ × V) : FH →ₗ[ℝ] Flux :=
    { toFun T i l j k m := ∑ d : Fin n,
        -(EuclideanSpace.proj i) ((G F.metric a p).inverse
          (T ((G F'.metric a p).inverse (EuclideanSpace.proj d)))) * kp a p d l j k m
      map_add' T T' := by
        ext i l j k m
        simp only [Flux, Raw, ContinuousLinearMap.add_apply, map_add, PiLp.add_apply, Pi.add_apply, neg_add,
          add_mul, Finset.sum_add_distrib]
      map_smul' r T := by
        ext i l j k m
        simp only [Flux, Raw, ContinuousLinearMap.smul_apply, map_smul, PiLp.smul_apply, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring }
  let lA (a : M) (p : ℝ × V) : FA →ₗ[ℝ] Flux :=
    { toFun T i l j k m := ∑ d, ai F.metric a p i d *
        act (ag T) (raw (Rbar' a p)) d l j k m
      map_add' T T' := by
        ext i l j k m
        simp only [Flux, Raw, act, ag, ContinuousLinearMap.add_apply, map_add, PiLp.add_apply, Pi.add_apply, add_mul,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
        ring
      map_smul' r T := by
        ext i l j k m
        simp only [Flux, Raw, act, ag, ContinuousLinearMap.smul_apply, map_smul, PiLp.smul_apply, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro b _
        ring }
  let lS (a : M) (p : ℝ × V) : FS →ₗ[ℝ] Flux :=
    { toFun T i l j k m := ∑ d, ai F.metric a p i d *
        act (gamma F.metric F.connection a p) (raw T) d l j k m
      map_add' T T' := by
        ext i l j k m
        simp only [Flux, Raw, act, raw, ContinuousLinearMap.add_apply, map_add, PiLp.add_apply, Pi.add_apply, mul_add,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub]
        ring
      map_smul' r T := by
        ext i l j k m
        simp only [Flux, Raw, act, raw, ContinuousLinearMap.smul_apply, map_smul, PiLp.smul_apply, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro b _
        ring }
  let lD (a : M) (p : ℝ × V) : (Fin dS × Fin n → ℝ) →ₗ[ℝ] Flux :=
    { toFun d i l j k m := ∑ b, ai F.metric a p i b * ∑ β : Fin dS,
        raw (qS.symm (EuclideanSpace.single β 1)) l j k m * d (β, b)
      map_add' d d' := by
        ext i l j k m
        simp only [Flux, Raw, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' r d := by
        ext i l j k m
        simp only [Flux, Raw, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro β _
        ring }
  let lE (a : M) (p : ℝ × V) : FA →ₗ[ℝ] Raw :=
    { toFun T := div (ag T) (vp a p)
      map_add' T T' := by
        ext l j k m
        simp only [Flux, Raw, div, act, ag, ContinuousLinearMap.add_apply, map_add, PiLp.add_apply, Pi.add_apply,
          add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring
      map_smul' r T := by
        ext l j k m
        simp only [Flux, Raw, div, act, ag, ContinuousLinearMap.smul_apply, map_smul, PiLp.smul_apply, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_add]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        · apply Finset.sum_congr rfl
          intro b _
          ring
        · apply Finset.sum_congr rfl
          intro b _
          ring }
  let rd (a : M) (p : ℝ × V) : Flux →ₗ[ℝ] (Fin dS → ℝ) :=
    contraction.comp (rawDivergenceAction (gamma F.metric F.connection a p))
  let bH := fun β : Fin dH => qH.symm (EuclideanSpace.single β 1)
  let bA := fun β : Fin dA => qA.symm (EuclideanSpace.single β 1)
  let bS := fun β : Fin dS => qS.symm (EuclideanSpace.single β 1)
  let bD : (Fin dS × Fin n) → (Fin dS × Fin n → ℝ) := fun β => Pi.single β (1 : ℝ)
  let udH := fun a p (α : Fin dS × Fin n) β => contraction (lH a p (bH β) α.2) α.1
  let udA := fun a p (α : Fin dS × Fin n) β => contraction (lA a p (bA β) α.2) α.1
  let udS := fun a p (α : Fin dS × Fin n) β => contraction (lS a p (bS β) α.2) α.1
  let cd := fun a p α β => rd a p (lD a p (bD β)) α
  let ch := fun a p α β => rd a p (lH a p (bH β)) α
  let ca := fun a p α β => rd a p (lA a p (bA β)) α + contraction (lE a p (bA β)) α
  let cs := fun a p α β => rd a p (lS a p (bS β)) α
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
  have hbaseS (a : M) : (c a).source ⊆ (eS a).baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx, hx⟩
  have hbaseT (a : M) {z : V} (hz : z ∈ (c a).target) :
      (c a).symm z ∈ (eT a).baseSet := by
    simpa only [eT, c, V, TangentBundle.trivializationAt_baseSet] using (c a).map_target hz
  have hchartK (a : M) (ha : a ∈ s) : ContinuousOn
      (fun p : ℝ × V => (p.1, (c a).symm p.2)) (K ×ˢ Q a) :=
    continuousOn_fst.prodMk ((c a).continuousOn_symm.comp continuousOn_snd
      (fun p hp => (hQ a ha).2 hp.2))
  have hginv (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) (a : M) (ha : a ∈ s) :
      ContinuousOn (fun p => (G g a p).inverse) (K ×ˢ Q a) := by
    simpa only [G, eH, FH, BH, V, hom_trivializationAt_apply, Function.comp_def] using
      (contMDiffOn_family_metric_frame_inverse hg a).2.2.continuousOn.comp
        (hchartK a ha) (fun p hp => ⟨hKJ hp.1, hbaseT a ((hQ a ha).2 hp.2)⟩)
  have hai (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) (a : M) (ha : a ∈ s) (i d) :
      ContinuousOn (fun p => ai g a p i d) (K ×ˢ Q a) :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn
      ((hginv g hg a ha).clm_apply continuousOn_const)
  have hframe (a : M) (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (frame a i)) (eT a).baseSet := by
    rw [(eT a).contMDiffOn_section_baseSet_iff (IB := 𝓡 n) (n := ∞)]
    refine (contMDiffOn_const (c := e i)).congr ?_
    intro y hy
    simpa [frame, Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd ((eT a).apply_mk_symm hy (e i))
  have hgamma (g : ℝ → RiemannianMetric n M)
      (D : (t : ℝ) → LeviCivitaData (g t))
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J'))
      (a : M) (ha : a ∈ s) (i j l : Fin n) :
      ContinuousOn (fun p => gamma g D a p i j l) (K ×ˢ Q a) := by
    have hs := contMDiffOn_connection_family_apply hg D (eT a).open_baseSet
      (frame a j) (frame a i) (hframe a j) (hframe a i)
    have hmaps : MapsTo (fun p : ℝ × M => TotalSpace.mk' V p.2
        ((D p.1).connection (frame a j) p.2 (frame a i p.2)))
        ((J ∩ J') ×ˢ (eT a).baseSet) (eT a).source := by
      exact fun p hp => ((eT a).mem_source).mpr hp.2
    have hc := ((eT a).contMDiffOn_iff hmaps).mp hs
    have hh : ContinuousOn (fun p : ℝ × V =>
        (eT a).continuousLinearMapAt ℝ ((c a).symm p.2)
          ((D p.1).connection (frame a j) ((c a).symm p.2)
            (frame a i ((c a).symm p.2)))) (K ×ˢ Q a) := by
      apply (hc.2.continuousOn.comp (hchartK a ha) (fun p hp =>
        ⟨hKJ hp.1, hbaseT a ((hQ a ha).2 hp.2)⟩)).congr
      intro p hp
      exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ (eT a)
        (hbaseT a ((hQ a ha).2 hp.2)) _
    exact (EuclideanSpace.proj l).continuous.comp_continuousOn hh
  obtain ⟨R1, hR1, hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  have hR'eq : R1 = R' := by
    funext t x
    ext u v w
    exact (hR1 t x u v w).trans (hR' t x u v w).symm
  rw [hR'eq] at hR'sm
  have hrsm (a : M) : ContDiffOn ℝ ∞ (Rbar' a) (J' ×ˢ (c a).target) := by
    have hh := contDiffOn_family_bundle_coordinates (E := BS) qS R' hR'sm a (hbaseS a)
    simpa only [Function.comp_def, Rbar', ContinuousLinearEquiv.symm_apply_apply] using
      qS.symm.contDiff.comp_contDiffOn hh
  have hrraw (a : M) (l j k m : Fin n) : ContDiffOn ℝ ∞
      (fun p => raw (Rbar' a p) l j k m) (J' ×ˢ (c a).target) := by
    change ContDiffOn ℝ ∞ ((EuclideanSpace.proj l) ∘
      (fun p => Rbar' a p (e j) (e k) (e m))) (J' ×ˢ (c a).target)
    exact ContDiffOn.continuousLinearMap_comp (EuclideanSpace.proj l)
      ((((hrsm a).clm_apply (contDiffOn_const (c := e j))).clm_apply
        (contDiffOn_const (c := e k))).clm_apply (contDiffOn_const (c := e m)))
  have hpartial (a : M) (d l j k m : Fin n) : ContinuousOn
      (fun p : ℝ × V => fderiv ℝ (fun z => raw (Rbar' a (p.1, z)) l j k m)
        p.2 (e d)) (J' ×ˢ (c a).target) := by
    let r := fun p : ℝ × V => raw (Rbar' a p) l j k m
    have hr : ContDiffOn ℝ ∞ r (J' ×ˢ (c a).target) := hrraw a l j k m
    have hw : ContDiffOn ℝ ∞ (fun p : ℝ × V =>
        fderivWithin ℝ (fun z => r (p.1, z)) (c a).target p.2 (e d))
        (J' ×ˢ (c a).target) := by
      intro p hp
      have hh : ContDiffWithinAt ℝ ∞ (fun q : (ℝ × V) × V => r (q.1.1, q.2))
          ((J' ×ˢ (c a).target) ×ˢ (c a).target) (p, p.2) :=
        (hr p hp).comp (g := r) (f := fun q : (ℝ × V) × V => (q.1.1, q.2))
          (p, p.2) (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
          (fun (q : (ℝ × V) × V)
            (hq : q ∈ (J' ×ˢ (c a).target) ×ˢ (c a).target) => ⟨hq.1.1, hq.2⟩)
      exact hh.fderivWithin_apply contDiffWithinAt_snd contDiffWithinAt_const
        (c a).open_target.uniqueDiffOn (by simp) hp (fun q hq => hq.2)
    apply hw.continuousOn.congr
    intro p hp
    change fderiv ℝ (fun z => r (p.1, z)) p.2 _ =
      fderivWithin ℝ (fun z => r (p.1, z)) (c a).target p.2 _
    rw [fderivWithin_of_mem_nhds ((c a).open_target.mem_nhds hp.2)]
  have hrawcont (a : M) (ha : a ∈ s) (l j k m : Fin n) : ContinuousOn
      (fun p => raw (Rbar' a p) l j k m) (K ×ˢ Q a) :=
    (hrraw a l j k m).continuousOn.mono
      (Set.prod_mono (fun t ht => (hKJ ht).2) (hQ a ha).2)
  have hact {X : Type} [TopologicalSpace X] {L : Set X}
      (g : X → Fin n → Fin n → Fin n → ℝ) (T : X → Raw)
      (hg : ∀ i j l, ContinuousOn (fun x => g x i j l) L)
      (hT : ∀ l j k m, ContinuousOn (fun x => T x l j k m) L) (d l j k m) :
      ContinuousOn (fun x => act (g x) (T x) d l j k m) L := by
    exact continuousOn_finsetSum _ (fun p _ =>
      ((((hg d p l).mul (hT p j k m)).sub ((hg d j p).mul (hT l p k m))).sub
        ((hg d k p).mul (hT l j p m))).sub ((hg d m p).mul (hT l j k p)))
  have hkp (a : M) (ha : a ∈ s) (d l j k m) :
      ContinuousOn (fun p => kp a p d l j k m) (K ×ˢ Q a) :=
    ((hpartial a d l j k m).mono
      (Set.prod_mono (fun t ht => (hKJ ht).2) (hQ a ha).2)).add
      (hact _ _ (hgamma F'.metric F'.connection hF' a ha) (hrawcont a ha) d l j k m)
  have hvp (a : M) (ha : a ∈ s) (i l j k m) :
      ContinuousOn (fun p => vp a p i l j k m) (K ×ˢ Q a) :=
    continuousOn_finsetSum _ (fun d _ => (hai F'.metric hF' a ha i d).mul (hkp a ha d l j k m))
  have hlH (a : M) (ha : a ∈ s) (T : FH) (i l j k m) :
      ContinuousOn (fun p => lH a p T i l j k m) (K ×ˢ Q a) := by
    dsimp only [lH, LinearMap.coe_mk, AddHom.coe_mk]
    apply continuousOn_finsetSum
    intro d _
    exact (((EuclideanSpace.proj i).continuous.comp_continuousOn
      ((hginv F.metric hF a ha).clm_apply
        (T.continuous.comp_continuousOn ((hginv F'.metric hF' a ha).clm_apply
          continuousOn_const)))).neg).mul (hkp a ha d l j k m)
  have hlA (a : M) (ha : a ∈ s) (T : FA) (i l j k m) :
      ContinuousOn (fun p => lA a p T i l j k m) (K ×ˢ Q a) := by
    dsimp only [lA, LinearMap.coe_mk, AddHom.coe_mk]
    exact continuousOn_finsetSum _ (fun d _ => (hai F.metric hF a ha i d).mul
      (hact (fun _ => ag T) (fun p => raw (Rbar' a p))
        (fun _ _ _ => continuousOn_const) (hrawcont a ha) d l j k m))
  have hlS (a : M) (ha : a ∈ s) (T : FS) (i l j k m) :
      ContinuousOn (fun p => lS a p T i l j k m) (K ×ˢ Q a) := by
    dsimp only [lS, LinearMap.coe_mk, AddHom.coe_mk]
    exact continuousOn_finsetSum _ (fun d _ => (hai F.metric hF a ha i d).mul
      (hact (gamma F.metric F.connection a) (fun _ => raw T)
        (hgamma F.metric F.connection hF a ha) (fun _ _ _ _ => continuousOn_const) d l j k m))
  have hlD (a : M) (ha : a ∈ s) (T : Fin dS × Fin n → ℝ) (i l j k m) :
      ContinuousOn (fun p => lD a p T i l j k m) (K ×ˢ Q a) := by
    dsimp only [lD, LinearMap.coe_mk, AddHom.coe_mk]
    exact continuousOn_finsetSum _ (fun d _ => (hai F.metric hF a ha i d).mul continuousOn_const)
  have hdiv {X : Type} [TopologicalSpace X] {L : Set X}
      (g : X → Fin n → Fin n → Fin n → ℝ) (T : X → Flux)
      (hg : ∀ i j l, ContinuousOn (fun x => g x i j l) L)
      (hT : ∀ i l j k m, ContinuousOn (fun x => T x i l j k m) L) (l j k m) :
      ContinuousOn (fun x => div (g x) (T x) l j k m) L :=
    continuousOn_finsetSum _ (fun i _ =>
      (hact _ _ hg (hT i) i l j k m).add
        (continuousOn_finsetSum _ (fun p _ => (hg i p i).mul (hT p l j k m))))
  have hcontract {X : Type} [TopologicalSpace X] {L : Set X} (T : X → Raw)
      (hT : ∀ l j k m, ContinuousOn (fun x => T x l j k m) L) (α) :
      ContinuousOn (fun x => contraction (T x) α) L := by
    dsimp only [contraction, rawCurvatureContraction, LinearMap.coe_mk, AddHom.coe_mk]
    exact continuousOn_finsetSum _ (fun l _ => continuousOn_finsetSum _ (fun j _ =>
      continuousOn_finsetSum _ (fun k _ => continuousOn_finsetSum _ (fun m _ =>
        continuousOn_const.mul (hT l j k m)))))
  have hrd (a : M) (ha : a ∈ s) (T : (ℝ × V) → Flux)
      (hT : ∀ i l j k m, ContinuousOn (fun p => T p i l j k m) (K ×ˢ Q a)) (α) :
      ContinuousOn (fun p => rd a p (T p) α) (K ×ˢ Q a) := by
    change ContinuousOn (fun p => contraction
      (div (gamma F.metric F.connection a p) (T p)) α) (K ×ˢ Q a)
    exact hcontract (fun p => div (gamma F.metric F.connection a p) (T p))
      (hdiv (gamma F.metric F.connection a) T (hgamma F.metric F.connection hF a ha) hT) α
  let cU : M → (ℝ × V) → (Fin dS × Fin n) → (Fin dH ⊕ (Fin dA ⊕ Fin dS)) → ℝ :=
    fun a p α => Sum.elim (udH a p α) (Sum.elim (udA a p α) (udS a p α))
  have hcU (a : M) (ha : a ∈ s) (α) (β) :
      ContinuousOn (fun p => cU a p α β) (K ×ˢ Q a) := by
    rcases β with β | β | β
    · exact hcontract _ (hlH a ha (bH β) α.2) α.1
    · exact hcontract _ (hlA a ha (bA β) α.2) α.1
    · exact hcontract _ (hlS a ha (bS β) α.2) α.1
  obtain ⟨CU, hCU, hCUbound⟩ := exists_finite_compact_family_square_sum_bound s
    (fun a => K ×ˢ Q a) (fun a ha => hK.prod (hQ a ha).1) cU hcU
  have hcd (a : M) (ha : a ∈ s) (α β) :
      ContinuousOn (fun p => cd a p α β) (K ×ˢ Q a) := hrd a ha _ (hlD a ha (bD β)) α
  have hch (a : M) (ha : a ∈ s) (α β) :
      ContinuousOn (fun p => ch a p α β) (K ×ˢ Q a) := hrd a ha _ (hlH a ha (bH β)) α
  have hca (a : M) (ha : a ∈ s) (α β) :
      ContinuousOn (fun p => ca a p α β) (K ×ˢ Q a) := by
    have hsecond : ContinuousOn (fun p => contraction (lE a p (bA β)) α) (K ×ˢ Q a) := by
      apply hcontract
      intro l j k m
      change ContinuousOn (fun p => div (ag (bA β)) (vp a p) l j k m) (K ×ˢ Q a)
      exact hdiv (fun _ : ℝ × V => ag (bA β)) (vp a)
        (fun _ _ _ => continuousOn_const) (hvp a ha) l j k m
    exact (hrd a ha (fun p => lA a p (bA β)) (hlA a ha (bA β)) α).add hsecond
  have hcs (a : M) (ha : a ∈ s) (α β) :
      ContinuousOn (fun p => cs a p α β) (K ×ˢ Q a) := hrd a ha _ (hlS a ha (bS β)) α
  obtain ⟨C, hC, hCbound⟩ := exists_finite_compact_family_four_array_square_sum_bound s
    (fun a => K ×ˢ Q a) (fun a ha => hK.prod (hQ a ha).1) cd ch ca cs hcd hch hca hcs
  have hqcoord {d : ℕ} {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
      (q : T ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (x : T) :
      x = ∑ β : Fin d, q x β • q.symm (EuclideanSpace.single β 1) := by
    let b := PiLp.basisFun 2 ℝ (Fin d)
    have hb : q x = ∑ β : Fin d, q x β • EuclideanSpace.single β 1 := by
      simpa [b, PiLp.basisFun_repr, PiLp.basisFun_apply] using (b.sum_repr (q x)).symm
    calc
      x = q.symm (q x) := (q.symm_apply_apply x).symm
      _ = q.symm (∑ β : Fin d, q x β • EuclideanSpace.single β 1) := congrArg q.symm hb
      _ = _ := by simp only [map_sum, map_smul]
  have hLcoord {d : ℕ} {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
      (q : T ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (L : T →ₗ[ℝ] ℝ) (x : T) :
      L x = ∑ β : Fin d, L (q.symm (EuclideanSpace.single β 1)) * q x β := by
    calc
      L x = L (∑ β : Fin d, q x β • q.symm (EuclideanSpace.single β 1)) :=
        congrArg L (hqcoord q x)
      _ = ∑ β : Fin d, q x β * L (q.symm (EuclideanSpace.single β 1)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := Finset.sum_congr rfl (fun β _ => mul_comm _ _)
  have hw (a : M) (p : ℝ × V) :
      w a p = lH a p (Hbar a p) + lA a p (Abar a p) + lS a p (Sbar a p) := by
    funext i l j k m
    change w a p i l j k m = lH a p (Hbar a p) i l j k m +
      lA a p (Abar a p) i l j k m + lS a p (Sbar a p) i l j k m
    simp only [w, lH, lA, lS, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, Finset.sum_add_distrib, EuclideanSpace.coe_proj]
    ring
  refine ⟨CU, C + 1, hCU, by positivity, ?_⟩
  intro a ha t ht z hz
  let p : ℝ × V := (t, z)
  let values : Fin dH ⊕ (Fin dA ⊕ Fin dS) → ℝ :=
    Sum.elim (fun β => fH a β p) (Sum.elim (fun β => fA a β p) (fun β => fS a β p))
  let d := fun β : Fin dS × Fin n =>
    fderiv ℝ (fun y => fS a β.1 (t, y)) z (e β.2)
  have hlow (α : Fin dS × Fin n) : U a p α.1 α.2 = ∑ β, cU a p α β * values β := by
    let ellU : Flux →ₗ[ℝ] ℝ :=
      ((LinearMap.proj α.1).comp contraction).comp (LinearMap.proj α.2)
    have hh := hLcoord qH (ellU.comp (lH a p)) (Hbar a p)
    have hh' := hLcoord qA (ellU.comp (lA a p)) (Abar a p)
    have hh'' := hLcoord qS (ellU.comp (lS a p)) (Sbar a p)
    change ellU (lH a p (Hbar a p)) = ∑ β, udH a p α β * fH a β p at hh
    change ellU (lA a p (Abar a p)) = ∑ β, udA a p α β * fA a β p at hh'
    change ellU (lS a p (Sbar a p)) = ∑ β, udS a p α β * fS a β p at hh''
    change ellU (w a p) = _
    rw [hw, map_add, map_add, hh, hh', hh'']
    simp only [cU, values, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_assoc]
  have hvalues : (∑ β, (values β) ^ 2) = density a p := by
    simp only [values, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, density, add_assoc]
  constructor
  · have hh := (sum_sq_linear_combination_le (cU a p) values).trans
      (mul_le_mul_of_nonneg_right (hCUbound a ha p ⟨ht, hz⟩) (by positivity))
    rw [hvalues] at hh
    simpa only [← hlow, Fintype.sum_prod_type] using hh
  intro ε hε
  have hdrepr : d = ∑ β : Fin dS × Fin n, d β • bD β := by
    ext β
    simp [bD, Pi.single_apply]
  have hprincipal : principal a p = lD a p d := rfl
  have hlDrepr : lD a p d = ∑ β : Fin dS × Fin n, d β • lD a p (bD β) := by
    conv_lhs => rw [hdrepr]
    simp only [map_sum, map_smul]
  have hW (α : Fin dS) : W a p α =
      (∑ β, cd a p α β * d β) + (∑ β, ch a p α β * fH a β p) +
        (∑ β, ca a p α β * fA a β p) + (∑ β, cs a p α β * fS a β p) := by
    let ellR : Flux →ₗ[ℝ] ℝ := (LinearMap.proj α).comp (rd a p)
    let ellE : Raw →ₗ[ℝ] ℝ := (LinearMap.proj α).comp contraction
    have hh := hLcoord qH (ellR.comp (lH a p)) (Hbar a p)
    have hh' := hLcoord qA (ellR.comp (lA a p) + ellE.comp (lE a p)) (Abar a p)
    have hh'' := hLcoord qS (ellR.comp (lS a p)) (Sbar a p)
    change ellR (lH a p (Hbar a p)) = ∑ β, ch a p α β * fH a β p at hh
    change ellR (lA a p (Abar a p)) + ellE (lE a p (Abar a p)) =
      ∑ β, ca a p α β * fA a β p at hh'
    change ellR (lS a p (Sbar a p)) = ∑ β, cs a p α β * fS a β p at hh''
    have hd' : ellR (lD a p d) = ∑ β, cd a p α β * d β := by
      rw [hlDrepr, map_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [map_smul]
      change d β * ellR (lD a p (bD β)) = ellR (lD a p (bD β)) * d β
      exact mul_comm _ _
    have hshuffle (d h a s e : ℝ) : d + (h + a + s) + e = d + h + (a + e) + s := by
      ring
    calc
      W a p α = ellR (principal a p + w a p) + ellE (lE a p (Abar a p)) := by
        change ellE (rawDivergenceAction (gamma F.metric F.connection a p)
          (principal a p + w a p) + lE a p (Abar a p)) = _
        rw [map_add]
        rfl
      _ = ellR (lD a p d) + ellR (lH a p (Hbar a p)) +
          (ellR (lA a p (Abar a p)) + ellE (lE a p (Abar a p))) +
            ellR (lS a p (Sbar a p)) := by
        rw [hprincipal, hw, map_add, map_add, map_add]
        exact hshuffle _ _ _ _ _
      _ = _ := by rw [hd', hh, hh', hh'']
  let cR := fun α : Fin dS => Sum.elim (ch a p α) (Sum.elim (ca a p α) (cs a p α))
  have hc := hCbound a ha p ⟨ht, hz⟩
  have hcD : (∑ α, ∑ β, (cd a p α β) ^ 2) ≤ C := by
    have hH : 0 ≤ ∑ α, ∑ β, (ch a p α β) ^ 2 := by positivity
    have hA : 0 ≤ ∑ α, ∑ β, (ca a p α β) ^ 2 := by positivity
    have hS : 0 ≤ ∑ α, ∑ β, (cs a p α β) ^ 2 := by positivity
    linarith
  have hcR : (∑ α, ∑ β, (cR α β) ^ 2) ≤ C := by
    simp only [cR, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_add_distrib]
    have hD : 0 ≤ ∑ α, ∑ β, (cd a p α β) ^ 2 := by positivity
    linarith
  have hd := sum_two_mul_linear_combination_le (cd a p) (fun α => fS a α p) d hε hcD hC
  have hr := sum_two_mul_linear_combination_le cR (fun α => fS a α p) values
    (ε := 1) (by norm_num) hcR hC
  rw [hvalues] at hr
  have hgrad : (∑ β, (d β) ^ 2) = gradient a p := by
    simp only [d, gradient, p, Fintype.sum_prod_type]
  rw [hgrad] at hd
  have hden : (∑ α : Fin dS, (fS a α p) ^ 2) ≤ density a p := by
    dsimp only [density]
    have hH : 0 ≤ ∑ β : Fin dH, (fH a β p) ^ 2 := by positivity
    have hA : 0 ≤ ∑ β : Fin dA, (fA a β p) ^ 2 := by positivity
    linarith
  have hden0 : 0 ≤ density a p := by dsimp only [density]; positivity
  have hdb := mul_le_mul_of_nonneg_left hden (div_nonneg hC (le_of_lt hε))
  have hrb := mul_le_mul_of_nonneg_left hden hC
  have hCb : C / ε ≤ (C + 1) / ε := div_le_div_of_nonneg_right (by linarith) (le_of_lt hε)
  have hCb' := mul_le_mul_of_nonneg_right hCb hden0
  have hrate : (∑ α, 2 * fS a α p * W a p α) =
      (∑ α, 2 * fS a α p * (∑ β, cd a p α β * d β)) +
        (∑ α, 2 * fS a α p * (∑ β, cR α β * values β)) := by
    simp only [hW, cR, values, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      mul_add, Finset.sum_add_distrib]
    ring
  change (∑ α, 2 * fS a α p * W a p α) ≤
    ε * gradient a p + ((C + 1) / ε + (C + 1)) * density a p
  rw [hrate]
  simp only [one_mul, div_one] at hr
  nlinarith only [hd, hr, hdb, hrb, hCb']

end PoincareConjecture.Proofs.M03
