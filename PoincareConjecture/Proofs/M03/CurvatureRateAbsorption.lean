import PoincareConjecture.Proofs.M03.CurvatureRateCoordinateAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03

section CurvatureBundleCoordinates

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000

theorem ricciFlow_curvature_bundle_difference_coordinate_pde
    {n dS : ℕ} {M : Type u} [TopologicalSpace M]
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
    ∀ (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J')
      (R R' : (t : ℝ) → (x : M) → BS x),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
      ∀ x0 : M,
        let c := chartAt V x0
        let eT := trivializationAt V (TangentSpace (𝓡 n)) x0
        let eH := trivializationAt FH BH x0
        let eA := trivializationAt FA BA x0
        let eS := trivializationAt FS BS x0
        let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
        let frame := fun i x => eT.symmL ℝ x (e i)
        let G := fun (g : ℝ → RiemannianMetric n M) (p : ℝ × V) =>
          (eH (TotalSpace.mk' FH (c.symm p.2) ((g p.1).inner (c.symm p.2)))).2
        let ai := fun g p i d => ((G g p).inverse (EuclideanSpace.proj d)) i
        let gamma := fun (g : ℝ → RiemannianMetric n M)
          (D : (t : ℝ) → LeviCivitaData (g t)) (p : ℝ × V) i j l =>
          (eT.continuousLinearMapAt ℝ (c.symm p.2)
            ((D p.1).connection (frame j) (c.symm p.2) (frame i (c.symm p.2)))) l
        let Hbar := fun p : ℝ × V => (eH (TotalSpace.mk' FH (c.symm p.2)
          ((F.metric p.1).inner (c.symm p.2) - (F'.metric p.1).inner (c.symm p.2)))).2
        let Abar := fun p : ℝ × V => (eA (TotalSpace.mk' FA (c.symm p.2)
          (CovariantDerivative.difference (F.connection p.1).connection
            (F'.connection p.1).connection (c.symm p.2)))).2
        let Sbar := fun p : ℝ × V => (eS (TotalSpace.mk' FS (c.symm p.2)
          (R p.1 (c.symm p.2) - R' p.1 (c.symm p.2)))).2
        let Rbar := fun p : ℝ × V =>
          (eS (TotalSpace.mk' FS (c.symm p.2) (R p.1 (c.symm p.2)))).2
        let Rbar' := fun p : ℝ × V =>
          (eS (TotalSpace.mk' FS (c.symm p.2) (R' p.1 (c.symm p.2)))).2
        let raw := fun (T : FS) l j k m => (T (e j) (e k) (e m)) l
        let ag := fun (A : FA) i j l => (A (e j) (e i)) l
        let act := fun (g : Fin n → Fin n → Fin n → ℝ)
          (T : Fin n → Fin n → Fin n → Fin n → ℝ) d l j k m =>
            ∑ p : Fin n, (g d p l * T p j k m - g d j p * T l p k m -
              g d k p * T l j p m - g d m p * T l j k p)
        let div := fun (g : Fin n → Fin n → Fin n → ℝ)
          (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) l j k m =>
            ∑ i : Fin n, (act g (T i) i l j k m + ∑ p, g i p i * T p l j k m)
        let kp := fun (p : ℝ × V) d l j k m =>
          fderiv ℝ (fun z => raw (Rbar' (p.1, z)) l j k m) p.2 (e d) +
            act (gamma F'.metric F'.connection p) (raw (Rbar' p)) d l j k m
        let vp := fun p i l j k m => ∑ d, ai F'.metric p i d * kp p d l j k m
        let w := fun p i l j k m => ∑ d : Fin n,
          (ai F.metric p i d * act (gamma F.metric F.connection p)
              (raw (Sbar p)) d l j k m +
            -((G F.metric p).inverse
              (Hbar p ((G F'.metric p).inverse (EuclideanSpace.proj d)))) i *
                kp p d l j k m +
            ai F.metric p i d * act (ag (Abar p)) (raw (Rbar' p)) d l j k m)
        let fS := fun i p => qS (Sbar p) i
        let principal := fun (p : ℝ × V) i l j k m =>
          ∑ d, ai F.metric p i d * ∑ β : Fin dS,
            raw (qS.symm (EuclideanSpace.single β 1)) l j k m *
              fderiv ℝ (fun z => fS β (p.1, z)) p.2 (e d)
        let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m =>
          (EuclideanSpace.proj j).smulRight ((EuclideanSpace.proj k).smulRight
            ((EuclideanSpace.proj m).smulRight (e l)))
        let contract := fun (T : Fin n → Fin n → Fin n → Fin n → ℝ) α =>
          ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α * T l j k m
        let U := fun p α i => contract (w p i) α
        let W := fun p α => contract
          (div (gamma F.metric F.connection p) (principal p + w p) +
            div (ag (Abar p)) (vp p)) α
        let ric := fun (T : FS) u v => ∑ k, (T (e k) u v) k
        let reaction := fun (A : (V →L[ℝ] ℝ) →L[ℝ] V) (T : FS) l j k m =>
          (∑ i : Fin n, ∑ d : Fin n, (A (EuclideanSpace.proj d)) i •
            (T (T (e j) (e k) (e i)) (e d) (e m) -
              (2 : ℝ) • T (e k) (e i) (T (e d) (e j) (e m)) +
              (2 : ℝ) • T (e i) (e j) (T (e k) (e d) (e m)) +
              ric T (T (e j) (e k) (e m)) (e i) • e d -
              ric T (e j) (e i) • T (e d) (e k) (e m) -
              ric T (e k) (e i) • T (e j) (e d) (e m) -
              ric T (e m) (e i) • T (e j) (e k) (e d))) l
        let Qrate := fun p α => contract
          (reaction (G F.metric p).inverse (Rbar p) -
            reaction (G F'.metric p).inverse (Rbar' p)) α
        ∀ t ∈ interior (J ∩ J'),
          (∀ α i, ContDiffOn ℝ 1 (fun z => U (t, z) α i) c.target) ∧
          (∀ α, ContinuousOn (fun z => W (t, z) α + Qrate (t, z) α) c.target) ∧
          (∀ α, ∀ z ∈ c.target,
            fderiv ℝ (fS α) (t, z) (1, 0) =
              (∑ i, fderiv ℝ (fun y => ∑ d, ai F.metric (t, y) i d *
                fderiv ℝ (fun z => fS α (t, z)) y (e d)) z (e i)) +
              (∑ i, fderiv ℝ (fun y => U (t, y) α i) z (e i)) +
              (W (t, z) α + Qrate (t, z) α))
 := by
  classical
  intro V
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  intro FH FA FS BH BA BS
  let : NormedAddCommGroup FH := inferInstance
  let : NormedSpace ℝ FH := inferInstance
  let : NormedAddCommGroup FA := inferInstance
  let : NormedSpace ℝ FA := inferInstance
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : ∀ x, AddCommGroup (BH x) := inferInstance
  let : ∀ x, Module ℝ (BH x) := inferInstance
  let : ∀ x, AddCommGroup (BA x) := inferInstance
  let : ∀ x, Module ℝ (BA x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  intro qS J J' F F' R R' hR hR' x0
  intro c eT eH eA eS e frame G ai gamma Hbar Abar Sbar Rbar Rbar'
  intro raw ag act div kp vp w fS principal B contract U W ric reaction Qrate
  intro t ht
  have htF : t ∈ interior J := (interior_mono inter_subset_left) ht
  have htF' : t ∈ interior J' := (interior_mono inter_subset_right) ht
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let theta := eT.localFrameCoeff (𝓡 n) b
  have hbase (z : V) (hz : z ∈ c.target) : c.symm z ∈ eT.baseSet := by
    simpa only [eT, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hframe : eT.localFrame b = frame := by
    funext i x
    by_cases hx : x ∈ eT.baseSet
    · calc
        eT.localFrame b i x = eT.basisAt b hx i :=
          eT.localFrame_apply_of_mem_baseSet b hx
        _ = eT.symm x (e i) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply, e]
        _ = frame i x := (eT.symmL_apply hx _).symm
    · rw [eT.localFrame_apply_of_notMem b hx]
      exact (eT.symmL_apply_of_notMem hx (e i)).symm
  have htheta (x : M) (hx : x ∈ eT.baseSet) (i : Fin n)
      (v : TangentSpace (𝓡 n) x) :
      theta i x v = (eT.continuousLinearMapAt ℝ x v) i := by
    have hh := eT.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) b hx
      (FiberBundle.extend V v) i
    rw [FiberBundle.extend_apply_self] at hh
    change theta i x v = _ at hh
    rw [hh]
    simp only [Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, b, OrthonormalBasis.coe_toBasis_repr_apply,
      Trivialization.linearEquivAt_apply, Trivialization.continuousLinearMapAt_apply]
    rw [eT.linearMapAt_def_of_mem hx]
    rfl
  have hmodel (x : M) (hx : x ∈ eT.baseSet) (T : BS x) (u v w : V) :
      (eS (TotalSpace.mk' FS x T)).2 u v w =
        eT.continuousLinearMapAt ℝ x
          (T (eT.symmL ℝ x u) (eT.symmL ℝ x v) (eT.symmL ℝ x w)) := by
    have hxhom : x ∈ (trivializationAt (V →L[ℝ] V)
        (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) x0).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, hx⟩
    dsimp only [eS]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
      hx hx hxhom]
    rw [Trivialization.linearMapAt_apply, if_pos hxhom, hom_trivializationAt_apply]
    change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
      (TangentSpace (𝓡 n)) x0 x x0 x (T (eT.symm x u) (eT.symm x v)) w = _
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_apply]
    rw [Trivialization.symmL_apply (R := ℝ) eT hx u,
      Trivialization.symmL_apply (R := ℝ) eT hx v,
      Trivialization.symmL_apply (R := ℝ) eT hx w]
  have hmetric (g : ℝ → RiemannianMetric n M) (s : ℝ) (z : V)
      (hz : z ∈ c.target) (u v : V) :
      G g (s, z) u v = (g s).inner (c.symm z)
        (eT.symmL ℝ (c.symm z) u) (eT.symmL ℝ (c.symm z) v) := by
    dsimp only [G, eH]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) (hbase z hz) (hbase z hz) (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) eT (hbase z hz) u,
      ← Trivialization.symmL_apply (R := ℝ) eT (hbase z hz) v]
    simp only [Trivial.fiberBundle_trivializationAt',
      Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
  have hInv (g : ℝ → RiemannianMetric n M) (s : ℝ) (z : V)
      (hz : z ∈ c.target) : (G g (s, z)).IsInvertible := by
    apply isInvertible_bilinear_of_pos
    intro v hv
    rw [hmetric g s z hz]
    apply (g s).pos
    intro heq
    have hh := congrArg (eT.continuousLinearMapAt ℝ (c.symm z)) heq
    rw [Trivialization.continuousLinearMapAt_symmL eT (hbase z hz), map_zero] at hh
    exact hv hh
  have hHsub (s : ℝ) (z : V) (hz : z ∈ c.target) :
      Hbar (s, z) = G F.metric (s, z) - G F'.metric (s, z) := by
    ext u v
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      hmetric F.metric s z hz, hmetric F'.metric s z hz]
    dsimp only [Hbar, eH]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) (hbase z hz) (hbase z hz) (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) eT (hbase z hz) u,
      ← Trivialization.symmL_apply (R := ℝ) eT (hbase z hz) v]
    simp only [Trivial.fiberBundle_trivializationAt',
      Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
      ContinuousLinearMap.sub_apply]
  have hsubCoord (v w : V) (i : Fin n) : (v - w) i = v i - w i := rfl
  have hinvdiff (s : ℝ) (z : V) (hz : z ∈ c.target) (i d : Fin n) :
      ai F.metric (s, z) i d - ai F'.metric (s, z) i d =
        -((G F.metric (s, z)).inverse
          (Hbar (s, z) ((G F'.metric (s, z)).inverse (EuclideanSpace.proj d)))) i := by
    rw [hHsub s z hz]
    dsimp only [ai]
    simp only [ContinuousLinearMap.sub_apply, map_sub,
      (hInv F'.metric s z hz).self_apply_inverse,
      (hInv F.metric s z hz).inverse_apply_self, hsubCoord]
    ring
  have hSsub (s : ℝ) (z : V) (hz : z ∈ c.target) :
      Sbar (s, z) = Rbar (s, z) - Rbar' (s, z) := by
    have hxS : c.symm z ∈ eS.baseSet := by
      simp only [eS, FS, BS, hom_trivializationAt_baseSet]
      exact ⟨hbase z hz, hbase z hz, hbase z hz, hbase z hz⟩
    dsimp only [Sbar, Rbar, Rbar']
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) eS _ hxS, map_sub]
    rfl
  have hraw (s : ℝ) (z : V) (hz : z ∈ c.target) (l j k m : Fin n) :
      raw (Rbar (s, z)) l j k m =
        theta l (c.symm z) ((F.connection s).curvature (c.symm z)
          (frame j (c.symm z)) (frame k (c.symm z)) (frame m (c.symm z))) := by
    dsimp only [raw, Rbar]
    rw [hmodel _ (hbase z hz), htheta _ (hbase z hz), hR]
  have hraw' (s : ℝ) (z : V) (hz : z ∈ c.target) (l j k m : Fin n) :
      raw (Rbar' (s, z)) l j k m =
        theta l (c.symm z) ((F'.connection s).curvature (c.symm z)
          (frame j (c.symm z)) (frame k (c.symm z)) (frame m (c.symm z))) := by
    dsimp only [raw, Rbar']
    rw [hmodel _ (hbase z hz), htheta _ (hbase z hz), hR']
  have hag (s : ℝ) (z : V) (hz : z ∈ c.target) (i j l : Fin n) :
      ag (Abar (s, z)) i j l =
        gamma F.metric F.connection (s, z) i j l -
          gamma F'.metric F'.connection (s, z) i j l := by
    have hf := eT.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b j
    rw [hframe] at hf
    have hfj := (hf.contMDiffAt (eT.open_baseSet.mem_nhds (hbase z hz))).mdifferentiableAt
      (by simp)
    have hh := IsCovariantDerivativeOn.difference_apply
      (F.connection s).connection.isCovariantDerivativeOnUniv
      (F'.connection s).connection.isCovariantDerivativeOnUniv
      (mem_univ (c.symm z)) hfj
    change CovariantDerivative.difference (F.connection s).connection
      (F'.connection s).connection (c.symm z) (frame j (c.symm z)) =
        (F.connection s).connection (frame j) (c.symm z) -
          (F'.connection s).connection (frame j) (c.symm z) at hh
    dsimp only [ag, Abar, eA]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := TangentSpace (𝓡 n)) (hbase z hz) (hbase z hz) (hbase z hz)]
    rw [← Trivialization.symmL_apply (R := ℝ) eT (hbase z hz) (e j),
      ← Trivialization.symmL_apply (R := ℝ) eT (hbase z hz) (e i)]
    change (eT.continuousLinearMapAt ℝ (c.symm z)
      (CovariantDerivative.difference (F.connection s).connection
        (F'.connection s).connection (c.symm z) (frame j (c.symm z))
        (frame i (c.symm z)))) l = _
    have hh' := congrArg (fun L : TangentSpace (𝓡 n) (c.symm z) →L[ℝ]
        TangentSpace (𝓡 n) (c.symm z) => L (frame i (c.symm z))) hh
    have hc := congrArg (fun v : TangentSpace (𝓡 n) (c.symm z) =>
      (eT.continuousLinearMapAt ℝ (c.symm z) v) l) hh'
    simpa only [ContinuousLinearMap.sub_apply, map_sub, hsubCoord, gamma] using hc
  have hbaseS : c.source ⊆ eS.baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx, hx⟩
  obtain ⟨R0, hR0, hRsm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  obtain ⟨R1, hR1, hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  have hReq : R0 = R := by
    funext s x
    ext u v w
    exact (hR0 s x u v w).trans (hR s x u v w).symm
  have hR'eq : R1 = R' := by
    funext s x
    ext u v w
    exact (hR1 s x u v w).trans (hR' s x u v w).symm
  rw [hReq] at hRsm
  rw [hR'eq] at hR'sm
  have hRjoint : ContDiffOn ℝ ∞ (fun p => qS (Rbar p)) (J ×ˢ c.target) :=
    contDiffOn_family_bundle_coordinates (E := BS) qS R hRsm x0 hbaseS
  have hR'joint : ContDiffOn ℝ ∞ (fun p => qS (Rbar' p)) (J' ×ˢ c.target) :=
    contDiffOn_family_bundle_coordinates (E := BS) qS R' hR'sm x0 hbaseS
  have hSjoint : ContDiffOn ℝ ∞ (fun p => qS (Sbar p)) ((J ∩ J') ×ˢ c.target) := by
    apply ((hRjoint.mono (Set.prod_mono inter_subset_left subset_rfl)).sub
      (hR'joint.mono (Set.prod_mono inter_subset_right subset_rfl))).congr
    intro p hp
    rw [hSsub p.1 p.2 hp.2, map_sub]
  have hFSm (α : Fin dS) : ContDiffOn ℝ ∞ (fS α) ((J ∩ J') ×ˢ c.target) := by
    simpa only [fS, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) α).contDiff.comp_contDiffOn hSjoint
  have hRbarSpatial : ContDiffOn ℝ ∞ (fun z => Rbar (t, z)) c.target := by
    have hh := (qS.symm.contDiff.comp_contDiffOn hRjoint).comp
      (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨interior_subset htF, hz⟩)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, id_eq] using hh
  have hRbar'Spatial : ContDiffOn ℝ ∞ (fun z => Rbar' (t, z)) c.target := by
    have hh := (qS.symm.contDiff.comp_contDiffOn hR'joint).comp
      (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨interior_subset htF', hz⟩)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, id_eq] using hh
  have hqS (T : FS) : T = ∑ β : Fin dS,
      qS T β • qS.symm (EuclideanSpace.single β 1) := by
    have hb : qS T = ∑ β : Fin dS, qS T β • EuclideanSpace.single β 1 := by
      simpa only [PiLp.basisFun_repr, PiLp.basisFun_apply] using
        ((PiLp.basisFun 2 ℝ (Fin dS)).sum_repr (qS T)).symm
    calc
      T = qS.symm (qS T) := (qS.symm_apply_apply T).symm
      _ = qS.symm (∑ β, qS T β • EuclideanSpace.single β 1) := congrArg qS.symm hb
      _ = _ := by simp only [map_sum, map_smul]
  have hrawSexp (z : V) (l j k m : Fin n) :
      raw (Sbar (t, z)) l j k m = ∑ β : Fin dS,
        raw (qS.symm (EuclideanSpace.single β 1)) l j k m * fS β (t, z) := by
    have hh := congrArg (fun T : FS => (EuclideanSpace.proj l) (T (e j) (e k) (e m)))
      (hqS (Sbar (t, z)))
    simp only [sum_apply, smul_apply, map_sum, map_smul, smul_eq_mul,
      EuclideanSpace.coe_proj] at hh
    simpa only [raw, fS, mul_comm] using hh
  have hfS (β : Fin dS) : ContDiffOn ℝ ∞ (fun z => fS β (t, z)) c.target := by
    exact (hFSm β).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨interior_subset ht, hz⟩)
  have hrawSd (z : V) (hz : z ∈ c.target) (d l j k m : Fin n) :
      fderiv ℝ (fun y => raw (Sbar (t, y)) l j k m) z (e d) =
        ∑ β : Fin dS, raw (qS.symm (EuclideanSpace.single β 1)) l j k m *
          fderiv ℝ (fun y => fS β (t, y)) z (e d) := by
    have heq : (fun y => raw (Sbar (t, y)) l j k m) =
        (fun y => ∑ β : Fin dS, raw (qS.symm (EuclideanSpace.single β 1)) l j k m *
          fS β (t, y)) := funext (fun y => hrawSexp y l j k m)
    rw [heq]
    have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun β _ =>
      (((hfS β).contDiffAt (c.open_target.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.const_mul
        (raw (qS.symm (EuclideanSpace.single β 1)) l j k m))
    simpa only [sum_apply, smul_apply, smul_eq_mul] using
      congrArg (fun L => L (e d)) hh.fderiv
  have hprincipal (z : V) (hz : z ∈ c.target) (i l j k m : Fin n) :
      principal (t, z) i l j k m = ∑ d,
        ai F.metric (t, z) i d *
          fderiv ℝ (fun y => raw (Sbar (t, y)) l j k m) z (e d) := by
    dsimp only [principal]
    apply Finset.sum_congr rfl
    intro d _
    rw [hrawSd z hz d l j k m]
  have hactTensorSub (g : Fin n → Fin n → Fin n → ℝ)
      (T T' : FS) (d l j k m : Fin n) :
      act g (raw (T - T')) d l j k m =
        act g (raw T) d l j k m - act g (raw T') d l j k m := by
    dsimp only [act, raw]
    simp only [ContinuousLinearMap.sub_apply, hsubCoord, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hactGammaSub (g g' : Fin n → Fin n → Fin n → ℝ)
      (T : FS) (d l j k m : Fin n) :
      act (g - g') (raw T) d l j k m =
        act g (raw T) d l j k m - act g' (raw T) d l j k m := by
    dsimp only [act]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hrawR (l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => raw (Rbar (t, z)) l j k m) c.target := by
    exact (EuclideanSpace.proj l).contDiff.comp_contDiffOn
      (((hRbarSpatial.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hrawR' (l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => raw (Rbar' (t, z)) l j k m) c.target := by
    exact (EuclideanSpace.proj l).contDiff.comp_contDiffOn
      (((hRbar'Spatial.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hgradS (z : V) (hz : z ∈ c.target) (d l j k m : Fin n) :
      fderiv ℝ (fun y => raw (Sbar (t, y)) l j k m) z (e d) =
        fderiv ℝ (fun y => raw (Rbar (t, y)) l j k m) z (e d) -
          fderiv ℝ (fun y => raw (Rbar' (t, y)) l j k m) z (e d) := by
    have heq : (fun y => raw (Sbar (t, y)) l j k m) =ᶠ[𝓝 z]
        (fun y => raw (Rbar (t, y)) l j k m - raw (Rbar' (t, y)) l j k m) := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      rw [hSsub t y hy]
      simp only [raw, ContinuousLinearMap.sub_apply, hsubCoord]
    rw [heq.fderiv_eq]
    rw [fderiv_fun_sub
      (((hrawR l j k m).contDiffAt (c.open_target.mem_nhds hz)).differentiableAt (by simp))
      (((hrawR' l j k m).contDiffAt (c.open_target.mem_nhds hz)).differentiableAt (by simp))]
    rfl
  let vF := fun z i l j k m => ∑ d,
    ai F.metric (t, z) i d *
      (fderiv ℝ (fun y => raw (Rbar (t, y)) l j k m) z (e d) +
        act (gamma F.metric F.connection (t, z)) (raw (Rbar (t, z))) d l j k m)
  have hresidual (z : V) (hz : z ∈ c.target) (i l j k m : Fin n) :
      vF z i l j k m - vp (t, z) i l j k m - principal (t, z) i l j k m =
        w (t, z) i l j k m := by
    rw [hprincipal z hz i l j k m]
    dsimp only [vF, vp, kp, w]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [hgradS z hz d l j k m, hSsub t z hz,
      hactTensorSub, ← hinvdiff t z hz i d]
    have ha : ag (Abar (t, z)) =
        gamma F.metric F.connection (t, z) - gamma F'.metric F'.connection (t, z) := by
      funext i j l
      exact hag t z hz i j l
    rw [ha, hactGammaSub]
    ring
  have hframeSmooth (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (frame i)) eT.baseSet := by
    rw [← hframe]
    exact eT.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  let N := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let Rfield := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let covR := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N D P (Rfield D A B C) y - Rfield D (N D P A) B C y -
      Rfield D A (N D P B) C y - Rfield D A B (N D P C) y
  let rho := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (z : V) (l j k m : Fin n) =>
    theta l (c.symm z) (Rfield D (frame j) (frame k) (frame m) (c.symm z))
  let vg := fun (g : ℝ → RiemannianMetric n M) (D : (s : ℝ) → LeviCivitaData (g s))
      (s : ℝ) (z : V) (i l j k m : Fin n) =>
    theta l (c.symm z) (∑ d, ai g (s, z) i d •
      covR (D s) (frame d) (frame j) (frame k) (frame m) (c.symm z))
  let rbar := fun (RR : (s : ℝ) → (x : M) → BS x) (p : ℝ × V) =>
    (eS (TotalSpace.mk' FS (c.symm p.2) (RR p.1 (c.symm p.2)))).2
  have hrho {JJ : Set ℝ} (FF : RicciFlow n M JJ)
      (RR : (s : ℝ) → (x : M) → BS x)
      (hRR : ∀ s x u v w, RR s x u v w = (FF.connection s).curvature x u v w)
      (s : ℝ) (z : V) (hz : z ∈ c.target) (l j k m : Fin n) :
      rho (FF.connection s) z l j k m = raw (rbar RR (s, z)) l j k m := by
    dsimp only [rho, Rfield, raw, rbar]
    rw [hmodel _ (hbase z hz), htheta _ (hbase z hz), hRR]
    exact congrArg (fun v => (eT.continuousLinearMapAt ℝ (c.symm z) v) l)
      (curvature_eq_curvatureOnFields (FF.connection s) eT.open_baseSet
        (frame j) (frame k) (frame m) (hframeSmooth j) (hframeSmooth k)
        (hframeSmooth m) (hbase z hz)).symm
  have hvg {JJ : Set ℝ} (FF : RicciFlow n M JJ)
      (RR : (s : ℝ) → (x : M) → BS x)
      (hRR : ∀ s x u v w, RR s x u v w = (FF.connection s).curvature x u v w)
      (s : ℝ) (z : V) (hz : z ∈ c.target) (i l j k m : Fin n) :
      vg FF.metric FF.connection s z i l j k m =
        ∑ d, ai FF.metric (s, z) i d *
          (fderiv ℝ (fun y => raw (rbar RR (s, y)) l j k m) z (e d) +
            act (gamma FF.metric FF.connection (s, z))
              (raw (rbar RR (s, z))) d l j k m) := by
    dsimp only [vg]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    have hc := curvature_covariant_derivative_coordinates (FF.connection s) x0 z hz d l j k m
    dsimp only at hc
    rw [hframe] at hc
    change theta l (c.symm z)
      (covR (FF.connection s) (frame d) (frame j) (frame k) (frame m) (c.symm z)) =
      fderiv ℝ (fun y => rho (FF.connection s) y l j k m) z (e d) +
        act (fun i j l => theta l (c.symm z)
          ((FF.connection s).connection (frame j) (c.symm z) (frame i (c.symm z))))
          (rho (FF.connection s) z) d l j k m at hc
    have hg : (fun i j l => theta l (c.symm z)
        ((FF.connection s).connection (frame j) (c.symm z) (frame i (c.symm z)))) =
          gamma FF.metric FF.connection (s, z) := by
      funext i j l
      exact htheta _ (hbase z hz) l _
    have hv : rho (FF.connection s) z = raw (rbar RR (s, z)) := by
      funext l j k m
      exact hrho FF RR hRR s z hz l j k m
    have heq : (fun y => rho (FF.connection s) y l j k m) =ᶠ[𝓝 z]
        (fun y => raw (rbar RR (s, y)) l j k m) := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      exact hrho FF RR hRR s y hy l j k m
    rw [hg, hv, heq.fderiv_eq] at hc
    exact hc
  let sigma := fun s z l j k m => rho (F.connection s) z l j k m -
    rho (F'.connection s) z l j k m
  let P := fun z i l j k m => ∑ d, ai F.metric (t, z) i d *
    fderiv ℝ (fun y => sigma t y l j k m) z (e d)
  let Uraw := fun z i l j k m =>
    vg F.metric F.connection t z i l j k m -
      vg F'.metric F'.connection t z i l j k m - P z i l j k m
  have hsigma (s : ℝ) (z : V) (hz : z ∈ c.target) (l j k m : Fin n) :
      sigma s z l j k m = raw (Sbar (s, z)) l j k m := by
    dsimp only [sigma]
    rw [hrho F R hR s z hz, hrho F' R' hR' s z hz, hSsub s z hz]
    simp only [raw, ContinuousLinearMap.sub_apply, PiLp.sub_apply]
    rfl
  have hP (z : V) (hz : z ∈ c.target) (i l j k m : Fin n) :
      P z i l j k m = principal (t, z) i l j k m := by
    rw [hprincipal z hz]
    dsimp only [P]
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    have heq : (fun y => sigma t y l j k m) =ᶠ[𝓝 z]
        (fun y => raw (Sbar (t, y)) l j k m) := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      exact hsigma t y hy l j k m
    rw [heq.fderiv_eq]
  have hUraw (z : V) (hz : z ∈ c.target) (i l j k m : Fin n) :
      Uraw z i l j k m = w (t, z) i l j k m := by
    dsimp only [Uraw]
    rw [hvg F R hR t z hz, hvg F' R' hR' t z hz, hP z hz]
    exact hresidual z hz i l j k m
  let Qg := fun (g : ℝ → RiemannianMetric n M) (D : (s : ℝ) → LeviCivitaData (g s))
      (s : ℝ) (z : V) (l j k m : Fin n) =>
    let x := c.symm z
    let T := (D s).curvature x
    let u := frame j x
    let v := frame k x
    let r := frame m x
    theta l x (∑ i : Fin n, ∑ d : Fin n, ai g (s, z) i d •
      (T (T u v (frame i x)) (frame d x) r -
        (2 : ℝ) • T v (frame i x) (T (frame d x) u r) +
        (2 : ℝ) • T (frame i x) u (T v (frame d x) r) +
        (D s).ricci x (T u v r) (frame i x) • frame d x -
        (D s).ricci x u (frame i x) • T (frame d x) v r -
        (D s).ricci x v (frame i x) • T u (frame d x) r -
        (D s).ricci x r (frame i x) • T u v (frame d x)))
  have hQg {JJ : Set ℝ} (FF : RicciFlow n M JJ)
      (RR : (s : ℝ) → (x : M) → BS x)
      (hRR : ∀ s x u v w, RR s x u v w = (FF.connection s).curvature x u v w)
      (s : ℝ) (z : V) (hz : z ∈ c.target) (l j k m : Fin n) :
      Qg FF.metric FF.connection s z l j k m =
        reaction (G FF.metric (s, z)).inverse (rbar RR (s, z)) l j k m := by
    let A := eT.linearEquivAt ℝ (c.symm z) (hbase z hz)
    have hf (i : Fin n) : A (frame i (c.symm z)) = e i := by
      dsimp only [frame]
      rw [eT.symmL_apply (hbase z hz)]
      exact A.apply_symm_apply (e i)
    have hh := curvature_reaction_frame_coordinates_eq_model (FF.connection s)
      x0 (c.symm z) (hbase z hz) (RR s (c.symm z)) (hRR s (c.symm z))
      (frame j (c.symm z)) (frame k (c.symm z)) (frame m (c.symm z))
    dsimp only at hh
    rw [hframe] at hh
    change A _ = _ at hh
    dsimp only [A, eT, V, e] at hf
    simp only [hf] at hh
    have hscalar := congrArg (fun v : V => (EuclideanSpace.proj l) v) hh
    dsimp only [Qg]
    rw [htheta _ (hbase z hz)]
    rw [Trivialization.continuousLinearMapAt_apply, eT.linearMapAt_def_of_mem (hbase z hz)]
    simpa only [Trivialization.continuousLinearMapAt_apply,
      Trivialization.linearMapAt_def_of_mem, LinearEquiv.coe_coe,
      G, eH, hom_trivializationAt_apply,
      ai, reaction, ric, rbar, eS, FS, BS, FH, BH, A, e, V,
      EuclideanSpace.coe_proj] using hscalar
  let Gamma := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (z : V) (i j l : Fin n) =>
    theta l (c.symm z) (D.connection (frame j) (c.symm z) (frame i (c.symm z)))
  have hGamma (g : ℝ → RiemannianMetric n M) (D : (s : ℝ) → LeviCivitaData (g s))
      (s : ℝ) (z : V) (hz : z ∈ c.target) :
      Gamma (D s) z = gamma g D (s, z) := by
    funext i j l
    exact htheta _ (hbase z hz) l _
  let action := fun (B : Fin n → Fin n → Fin n → ℝ)
      (v : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (l j k m : Fin n) =>
    ∑ i, ∑ p, (B i p i * v p l j k m + B i p l * v i p j k m -
      B i j p * v i l p k m - B i k p * v i l j p m - B i m p * v i l j k p)
  have haction (B : Fin n → Fin n → Fin n → ℝ)
      (v : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) : action B v = div B v := by
    funext l j k m
    dsimp only [action, div, act]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have htimeRaw (z : V) (hz : z ∈ c.target) (l j k m : Fin n) :
      HasDerivAt (fun s => raw (Sbar (s, z)) l j k m)
        ((∑ i, fderiv ℝ (fun y => principal (t, y) i l j k m) z (e i)) +
          (∑ i, fderiv ℝ (fun y => w (t, y) i l j k m) z (e i)) +
          (div (gamma F.metric F.connection (t, z))
              (principal (t, z) + w (t, z)) l j k m +
            div (ag (Abar (t, z))) (vp (t, z)) l j k m +
            reaction (G F.metric (t, z)).inverse (Rbar (t, z)) l j k m -
            reaction (G F'.metric (t, z)).inverse (Rbar' (t, z)) l j k m)) t := by
    have hs := hasDerivAt_ricciFlow_curvature_difference_divergence
      F F' htF htF' x0 z hz l j k m
    dsimp only at hs
    rw [hframe] at hs
    change HasDerivAt (fun s => sigma s z l j k m)
      ((∑ i, fderiv ℝ (fun y => P y i l j k m) z (e i)) +
        (∑ i, fderiv ℝ (fun y => Uraw y i l j k m) z (e i)) +
        (action (Gamma (F.connection t) z)
            (fun i l j k m => P z i l j k m + Uraw z i l j k m) l j k m +
          action (Gamma (F.connection t) z - Gamma (F'.connection t) z)
            (vg F'.metric F'.connection t z) l j k m +
          Qg F.metric F.connection t z l j k m - Qg F'.metric F'.connection t z l j k m)) t at hs
    have hPd (i : Fin n) :
        fderiv ℝ (fun y => P y i l j k m) z =
          fderiv ℝ (fun y => principal (t, y) i l j k m) z := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      exact hP y hy i l j k m
    have hUd (i : Fin n) :
        fderiv ℝ (fun y => Uraw y i l j k m) z =
          fderiv ℝ (fun y => w (t, y) i l j k m) z := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      exact hUraw y hy i l j k m
    have hsum : (fun i l j k m => P z i l j k m + Uraw z i l j k m) =
        principal (t, z) + w (t, z) := by
      funext i l j k m
      rw [hP z hz, hUraw z hz]
      rfl
    have hvg' : vg F'.metric F'.connection t z = vp (t, z) := by
      funext i l j k m
      exact hvg F' R' hR' t z hz i l j k m
    have hgamdiff : Gamma (F.connection t) z - Gamma (F'.connection t) z =
        ag (Abar (t, z)) := by
      rw [hGamma F.metric F.connection t z hz, hGamma F'.metric F'.connection t z hz]
      funext i j l
      exact (hag t z hz i j l).symm
    rw [hgamdiff] at hs
    simp only [hPd, hUd, hsum, hvg', hGamma F.metric F.connection t z hz,
      haction, hQg F R hR t z hz, hQg F' R' hR' t z hz] at hs
    exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun s => (hsigma s z hz l j k m).symm))
  have hcontractModel (T : FS) (α : Fin dS) : contract (raw T) α = qS T α :=
    curvature_contract_model_coordinate_expand qS T α
  have hcontractPrincipal (z : V) (i : Fin n) (α : Fin dS) :
      contract (principal (t, z) i) α =
        ∑ d, ai F.metric (t, z) i d *
          fderiv ℝ (fun y => fS α (t, y)) z (e d) := by
    apply curvature_contract_principal_algebra
      (fun l j k m => qS (B l j k m) α)
      (fun β => raw (qS.symm (EuclideanSpace.single β 1))) α
    intro β
    change contract (raw (qS.symm (EuclideanSpace.single β 1))) α = _
    rw [hcontractModel, ContinuousLinearEquiv.apply_symm_apply]
    simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
  have hprincipalSmooth (i l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => principal (t, z) i l j k m) c.target := by
    have hchart : ContMDiffOn 𝓘(ℝ, V) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun z : V => (t, c.symm z)) c.target :=
      contMDiffOn_const.prodMk (contMDiffOn_chart_symm (x := x0))
    have hinv : ContDiffOn ℝ ∞ (fun z => (G F.metric (t, z)).inverse) c.target := by
      simpa only [G, eH, FH, BH, V, hom_trivializationAt_apply, Function.comp_def] using
        ((contMDiffOn_family_metric_frame_inverse F.smooth x0).2.2.comp hchart
          (fun z hz => ⟨interior_subset htF, hbase z hz⟩)).contDiffOn
    apply ContDiffOn.sum
    intro d _
    exact ((EuclideanSpace.proj i).contDiff.comp_contDiffOn
      (hinv.clm_apply contDiffOn_const)).mul
      (ContDiffOn.sum (fun β _ => contDiffOn_const.mul
        (((hfS β).fderiv_of_isOpen c.open_target (by simp)).clm_apply contDiffOn_const)))
  have htJ : t ∈ J ∩ J' := interior_subset ht
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from inter_subset_right) subset_rfl)
  have hchart : ContMDiffOn 𝓘(ℝ, V) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : V => (t, c.symm z)) c.target :=
    contMDiffOn_const.prodMk (contMDiffOn_chart_symm (x := x0))
  have hGSpatial (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) :
      ContDiffOn ℝ ∞ (fun z => G g (t, z)) c.target := by
    simpa only [G, eH, FH, BH, V, hom_trivializationAt_apply, Function.comp_def] using
      ((contMDiffOn_family_metric_frame_inverse hg x0).2.1.comp hchart
        (fun z hz => ⟨htJ, hbase z hz⟩)).contDiffOn
  have hginv (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) :
      ContDiffOn ℝ ∞ (fun z => (G g (t, z)).inverse) c.target := by
    simpa only [G, eH, FH, BH, V, hom_trivializationAt_apply, Function.comp_def] using
      ((contMDiffOn_family_metric_frame_inverse hg x0).2.2.comp hchart
        (fun z hz => ⟨htJ, hbase z hz⟩)).contDiffOn
  have hai (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) (i d : Fin n) :
      ContDiffOn ℝ ∞ (fun z => ai g (t, z) i d) c.target := by
    simpa only [ai, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn
        ((hginv g hg).clm_apply (contDiffOn_const (c := EuclideanSpace.proj d)))
  have hgamma (g : ℝ → RiemannianMetric n M)
      (D : (r : ℝ) → LeviCivitaData (g r))
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) (i j l : Fin n) :
      ContDiffOn ℝ ∞ (fun z => gamma g D (t, z) i j l) c.target := by
    have hs := contMDiffOn_connection_family_apply hg D eT.open_baseSet
      (frame j) (frame i) (hframeSmooth j) (hframeSmooth i)
    have hmaps : MapsTo (fun p : ℝ × M => TotalSpace.mk' V p.2
        ((D p.1).connection (frame j) p.2 (frame i p.2)))
        ((J ∩ J') ×ˢ eT.baseSet) eT.source :=
      fun p hp => eT.mem_source.mpr hp.2
    have hc := (eT.contMDiffOn_iff hmaps).mp hs
    have hh : ContDiffOn ℝ ∞ (fun z : V => eT.continuousLinearMapAt ℝ (c.symm z)
        ((D t).connection (frame j) (c.symm z) (frame i (c.symm z)))) c.target := by
      apply ((hc.2.comp hchart (fun z hz => ⟨htJ, hbase z hz⟩)).contDiffOn).congr
      intro z hz
      exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ eT (hbase z hz) _
    exact (EuclideanSpace.proj l).contDiff.comp_contDiffOn hh
  have hHSpatial : ContDiffOn ℝ ∞ (fun z => Hbar (t, z)) c.target := by
    apply ((hGSpatial F.metric hF).sub (hGSpatial F'.metric hF')).congr
    intro z hz
    exact hHsub t z hz
  have hagSpatial (i j l : Fin n) :
      ContDiffOn ℝ ∞ (fun z => ag (Abar (t, z)) i j l) c.target := by
    apply ((hgamma F.metric F.connection hF i j l).sub
      (hgamma F'.metric F'.connection hF' i j l)).congr
    intro z hz
    exact hag t z hz i j l
  have hSSpatial : ContDiffOn ℝ ∞ (fun z => Sbar (t, z)) c.target := by
    apply (hRbarSpatial.sub hRbar'Spatial).congr
    intro z hz
    exact hSsub t z hz
  have hRawSmooth (T : V → FS) (hT : ContDiffOn ℝ ∞ T c.target) (l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => raw (T z) l j k m) c.target := by
    simpa only [raw, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp_contDiffOn
        (((hT.clm_apply (contDiffOn_const (c := e j))).clm_apply
          (contDiffOn_const (c := e k))).clm_apply (contDiffOn_const (c := e m)))
  have hact (g : V → Fin n → Fin n → Fin n → ℝ)
      (T : V → Fin n → Fin n → Fin n → Fin n → ℝ)
      (hg : ∀ i j l, ContDiffOn ℝ ∞ (fun z => g z i j l) c.target)
      (hT : ∀ l j k m, ContDiffOn ℝ ∞ (fun z => T z l j k m) c.target) (d l j k m) :
      ContDiffOn ℝ ∞ (fun z => act (g z) (T z) d l j k m) c.target :=
    ContDiffOn.sum (fun p _ =>
      ((((hg d p l).mul (hT p j k m)).sub ((hg d j p).mul (hT l p k m))).sub
        ((hg d k p).mul (hT l j p m))).sub ((hg d m p).mul (hT l j k p)))
  have hkp (d l j k m : Fin n) : ContDiffOn ℝ ∞ (fun z => kp (t, z) d l j k m) c.target :=
    (((hrawR' l j k m).fderiv_of_isOpen c.open_target (by simp)).clm_apply
      contDiffOn_const).add
      (hact _ _ (hgamma F'.metric F'.connection hF') hrawR' d l j k m)
  have hvp (i l j k m : Fin n) : ContDiffOn ℝ ∞ (fun z => vp (t, z) i l j k m) c.target :=
    ContDiffOn.sum (fun d _ => (hai F'.metric hF' i d).mul (hkp d l j k m))
  have hwSmooth (i l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => w (t, z) i l j k m) c.target := by
    apply ContDiffOn.sum
    intro d _
    exact (((hai F.metric hF i d).mul
      (hact _ _ (hgamma F.metric F.connection hF) (hRawSmooth _ hSSpatial) d l j k m)).add
      (((EuclideanSpace.proj i).contDiff.comp_contDiffOn
        ((hginv F.metric hF).clm_apply (hHSpatial.clm_apply
          ((hginv F'.metric hF').clm_apply contDiffOn_const)))).neg.mul
            (hkp d l j k m))).add
      ((hai F.metric hF i d).mul (hact _ _ hagSpatial hrawR' d l j k m))
  have hdiv (g : V → Fin n → Fin n → Fin n → ℝ)
      (T : V → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
      (hg : ∀ i j l, ContDiffOn ℝ ∞ (fun z => g z i j l) c.target)
      (hT : ∀ i l j k m, ContDiffOn ℝ ∞ (fun z => T z i l j k m) c.target) (l j k m) :
      ContDiffOn ℝ ∞ (fun z => div (g z) (T z) l j k m) c.target :=
    ContDiffOn.sum (fun i _ => (hact _ _ hg (hT i) i l j k m).add
      (ContDiffOn.sum (fun p _ => (hg i p i).mul (hT p l j k m))))
  have hcontract (T : V → Fin n → Fin n → Fin n → Fin n → ℝ)
      (hT : ∀ l j k m, ContDiffOn ℝ ∞ (fun z => T z l j k m) c.target) (α : Fin dS) :
      ContDiffOn ℝ ∞ (fun z => contract (T z) α) c.target :=
    ContDiffOn.sum (fun l _ => ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun k _ =>
      ContDiffOn.sum (fun m _ => contDiffOn_const.mul (hT l j k m)))))
  have hW (α : Fin dS) : ContDiffOn ℝ ∞ (fun z => W (t, z) α) c.target :=
    hcontract _ (fun l j k m =>
      (hdiv _ _ (hgamma F.metric F.connection hF)
        (fun i l j k m => (hprincipalSmooth i l j k m).add (hwSmooth i l j k m)) l j k m).add
      (hdiv _ _ hagSpatial hvp l j k m)) α
  have hric (T : V → FS) (hT : ContDiffOn ℝ ∞ T c.target)
      (a b : V → V) (ha : ContDiffOn ℝ ∞ a c.target) (hb : ContDiffOn ℝ ∞ b c.target) :
      ContDiffOn ℝ ∞ (fun z => ric (T z) (a z) (b z)) c.target := by
    apply ContDiffOn.sum
    intro k _
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn
        (((hT.clm_apply (contDiffOn_const (c := e k))).clm_apply ha).clm_apply hb)
  have hreaction (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J'))
      (T : V → FS) (hT : ContDiffOn ℝ ∞ T c.target) (l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => reaction (G g (t, z)).inverse (T z) l j k m) c.target := by
    dsimp only [reaction]
    change ContDiffOn ℝ ∞ ((EuclideanSpace.proj (𝕜 := ℝ) l) ∘ _) c.target
    apply (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp_contDiffOn
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro d _
    apply (hai g hg i d).smul
    have hev (a b r : Fin n) : ContDiffOn ℝ ∞ (fun z => T z (e a) (e b) (e r)) c.target :=
      ((hT.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const
    have h1 := ((hT.clm_apply (hev j k i)).clm_apply (contDiffOn_const (c := e d))).clm_apply
      (contDiffOn_const (c := e m))
    have h2 := (contDiffOn_const (c := (2 : ℝ))).smul
      (((hT.clm_apply (contDiffOn_const (c := e k))).clm_apply
        (contDiffOn_const (c := e i))).clm_apply (hev d j m))
    have h3 := (contDiffOn_const (c := (2 : ℝ))).smul
      (((hT.clm_apply (contDiffOn_const (c := e i))).clm_apply
        (contDiffOn_const (c := e j))).clm_apply (hev k d m))
    have h4 := (hric _ hT _ _ (hev j k m) (contDiffOn_const (c := e i))).smul
      (contDiffOn_const (c := e d))
    have h5 := (hric _ hT _ _ (contDiffOn_const (c := e j))
      (contDiffOn_const (c := e i))).smul (hev d k m)
    have h6 := (hric _ hT _ _ (contDiffOn_const (c := e k))
      (contDiffOn_const (c := e i))).smul (hev j d m)
    have h7 := (hric _ hT _ _ (contDiffOn_const (c := e m))
      (contDiffOn_const (c := e i))).smul (hev j k d)
    exact (((((h1.sub h2).add h3).add h4).sub h5).sub h6).sub h7
  have hQ (α : Fin dS) : ContDiffOn ℝ ∞ (fun z => Qrate (t, z) α) c.target :=
    hcontract _ (fun l j k m => (hreaction F.metric hF _ hRbarSpatial l j k m).sub
      (hreaction F'.metric hF' _ hRbar'Spatial l j k m)) α
  have hSpatial :
      (∀ α i, ContDiffOn ℝ 1 (fun z => U (t, z) α i) c.target) ∧
      (∀ α, ContinuousOn (fun z => W (t, z) α + Qrate (t, z) α) c.target) := by
    exact ⟨fun α i => (hcontract _ (hwSmooth i) α).of_le (by simp),
      fun α => ((hW α).add (hQ α)).continuousOn⟩
  refine ⟨hSpatial.1, hSpatial.2, ?_⟩
  intro α z hz
  let rp := fun l j k m => ∑ i,
    fderiv ℝ (fun y => principal (t, y) i l j k m) z (e i)
  let ru := fun l j k m => ∑ i,
    fderiv ℝ (fun y => w (t, y) i l j k m) z (e i)
  let low := fun l j k m =>
    div (gamma F.metric F.connection (t, z)) (principal (t, z) + w (t, z)) l j k m +
      div (ag (Abar (t, z))) (vp (t, z)) l j k m +
      reaction (G F.metric (t, z)).inverse (Rbar (t, z)) l j k m -
      reaction (G F'.metric (t, z)).inverse (Rbar' (t, z)) l j k m
  have htime : HasDerivAt (fun s => fS α (s, z)) (contract (rp + ru + low) α) t := by
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
          HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
            (htimeRaw z hz l j k m).const_mul (qS (B l j k m) α)))))
    exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun s => (hcontractModel (Sbar (s, z)) α).symm))
  have hdiff : fderiv ℝ (fS α) (t, z) (1, 0) = contract (rp + ru + low) α := by
    have hf := ((hFSm α).contDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) (c.open_target.mem_nhds hz))).differentiableAt
        (by simp)
    have hcurve : HasDerivAt (fun s : ℝ => (s, z)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    have hc : HasDerivAt (fun s => fS α (s, z))
        (fderiv ℝ (fS α) (t, z) (1, 0)) t := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
        hf.hasFDerivAt.comp_hasDerivAt t hcurve
    exact hc.unique htime
  have hPdiv : contract rp α =
      ∑ i, fderiv ℝ (fun y => ∑ d, ai F.metric (t, y) i d *
        fderiv ℝ (fun z => fS α (t, z)) y (e d)) z (e i) := by
    have hh := curvature_contract_divergence_algebra
      (fun l j k m => qS (B l j k m) α)
      (fun i l j k m y => principal (t, y) i l j k m) z
      (fun i l j k m => ((hprincipalSmooth i l j k m).contDiffAt
        (c.open_target.mem_nhds hz)).differentiableAt (by simp))
    change contract rp α = ∑ i,
      fderiv ℝ (fun y => contract (principal (t, y) i) α) z (e i) at hh
    simpa only [hcontractPrincipal] using hh
  have hUdiv : contract ru α =
      ∑ i, fderiv ℝ (fun y => U (t, y) α i) z (e i) := by
    exact curvature_contract_divergence_algebra
      (fun l j k m => qS (B l j k m) α)
      (fun i l j k m y => w (t, y) i l j k m) z
      (fun i l j k m => ((hwSmooth i l j k m).contDiffAt
        (c.open_target.mem_nhds hz)).differentiableAt (by simp))
  have hLow : contract low α = W (t, z) α + Qrate (t, z) α := by
    dsimp only [low, W, Qrate, contract]
    simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hadd (a b : Fin n → Fin n → Fin n → Fin n → ℝ) :
      contract (a + b) α = contract a α + contract b α := by
    simp only [contract, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hdiff, hadd, hadd, hPdiv, hUdiv, hLow]

end CurvatureBundleCoordinates

end PoincareConjecture.Proofs.M03
