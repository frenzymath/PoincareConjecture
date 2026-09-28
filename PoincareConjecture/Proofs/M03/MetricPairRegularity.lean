import PoincareConjecture.Proofs.M03.ConnectionFamily
import Mathlib.Analysis.Calculus.ContDiff.Operations









set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_family_vector_of_metric_pair
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {U : Set M} (hU : IsOpen U)
    (V : (p : ℝ × M) → TangentSpace (𝓡 n) p.2)
    (hV : ∀ (S : Set M), IsOpen S → S ⊆ U →
      ∀ (Y : (x : M) → TangentSpace (𝓡 n) x),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% Y) S →
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (g p.1).inner p.2 (V p) (Y p.2)) (J ×ˢ S)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) p.2 (V p)) (J ×ˢ U) := by
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2
  have hep : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
  let frame (a : EuclideanSpace ℝ (Fin n)) (x : M) : TangentSpace (𝓡 n) x :=
    e.symmL ℝ x a
  have hframe (a : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (frame a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro x hx
    simpa [frame, Trivialization.symmL_apply _ hx] using
      congrArg Prod.snd (e.apply_mk_symm hx a)
  let G (q : ℝ × M) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ) p.2 q.2 p.2 q.2
      ((g q.1).inner q.2)
  let B (q : ℝ × M) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((g q.1).inner q.2 (V q)).comp (e.symmL ℝ q.2)
  let C (q : ℝ × M) : EuclideanSpace ℝ (Fin n) :=
    (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2 (V q))).2
  have hG : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞
      G (J ×ˢ U) p := by
    have hg' := hg.mono (Set.prod_mono subset_rfl (subset_univ U))
    let H : ℝ × M →
        TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
      fun q => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        q.2 ((g q.1).inner q.2)
    have hmetric := (contMDiffWithinAt_hom_bundle H
      (s := J ×ˢ U) (x₀ := p)).mp (hg' p hp)
    simpa [G, H] using hmetric.2
  have hGinv (q : ℝ × M) (hq : q.2 ∈ e.baseSet) : (G q).IsInvertible := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(g q.1).toRiemannianMetric⟩
    rw [show G q =
        (e.continuousLinearEquivAt ℝ q.2 hq).arrowCongr
          (1 : ℝ ≃L[ℝ] ℝ) ∘L ((g q.1).inner q.2) ∘L
          (e.continuousLinearEquivAt ℝ q.2 hq).symm by
      ext a b
      dsimp [G]
      rw [inCoordinates_apply_eq₂
        (F₁ := EuclideanSpace ℝ (Fin n))
        (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hq hq (by simp)]
      simp [e]
      rfl]
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) q.2) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) q.2
    have hinj : Function.Injective ((g q.1).inner q.2).toLinearMap := by
      intro a b hab
      apply ext_inner_right ℝ
      intro c
      exact congrArg (fun L : TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ => L c) hab
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q.2) =
        Module.finrank ℝ (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ) := by
      calc
        _ = Module.finrank ℝ (Module.Dual ℝ (TangentSpace (𝓡 n) q.2)) :=
          Subspace.dual_finrank_eq.symm
        _ = _ := (LinearMap.toContinuousLinearMap :
          (TangentSpace (𝓡 n) q.2 →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
            (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ)).finrank_eq
    have hi : ((g q.1).inner q.2).IsInvertible :=
      ⟨(((g q.1).inner q.2).toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv,
        rfl⟩
    have hdual : ((e.continuousLinearEquivAt ℝ q.2 hq).arrowCongr
        (1 : ℝ ≃L[ℝ] ℝ) : (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ) →L[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv
    have hT : ((e.continuousLinearEquivAt ℝ q.2 hq).symm :
        EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) q.2).IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv
    exact hdual.comp (hi.comp hT)
  have hinv : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (fun q => (G q).inverse) (J ×ˢ U) p :=
    ContMDiffAt.comp_contMDiffWithinAt p
      (hGinv p hep).contDiffAt_map_inverse.contMDiffAt hG
  have hbase : ∀ᶠ q in 𝓝[J ×ˢ U] p, q.2 ∈ e.baseSet :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hep))
  have hsmall : J ×ˢ (U ∩ e.baseSet) ∈ 𝓝[J ×ˢ U] p := by
    filter_upwards [self_mem_nhdsWithin, hbase] with q hq hqe
    exact ⟨hq.1, hq.2, hqe⟩
  have hB : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ B (J ×ˢ U) p := by
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro a
    have hs := hV (U ∩ e.baseSet) (hU.inter e.open_baseSet) inter_subset_left
      (frame a) ((hframe a).mono inter_subset_right)
    exact (hs p ⟨hp.1, hp.2, hep⟩).mono_of_mem_nhdsWithin hsmall
  have hGC (q : ℝ × M) (hq : q.2 ∈ e.baseSet) : G q (C q) = B q := by
    ext a
    dsimp [G, B, C]
    rw [inCoordinates_apply_eq₂
      (F₁ := EuclideanSpace ℝ (Fin n))
      (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hq hq (by simp)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
    change (g q.1).inner q.2
      (e.symm q.2 ((e (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2 (V q))).2))
      (e.symm q.2 a) = (g q.1).inner q.2 (V q) (e.symmL ℝ q.2 a)
    rw [e.symm_apply_apply_mk hq, Trivialization.symmL_apply _ hq]
  have hC : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ C (J ×ˢ U) p := by
    apply (hinv.clm_apply hB).congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hbase] with q hq
    rw [← hGC q hq]
    symm
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      L (C q)) (hGinv q hq).inverse_comp_self
  exact Bundle.contMDiffWithinAt_totalSpace.mpr ⟨contMDiffWithinAt_snd, hC⟩


section FiniteSpatialJets

set_option synthInstance.maxHeartbeats 200000

theorem contDiffOn_spatial_jets_fderiv
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (k : ℕ) (f : ℝ → E → F)
    (hjets : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E => iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E =>
        iteratedFDeriv ℝ q (fun x => fderiv ℝ (f p.1) x) p.2) (J ×ˢ U) := by
  intro q
  let L : (E [×(q + 1)]→L[ℝ] F) →L[ℝ] (E [×q]→L[ℝ] (E →L[ℝ] F)) :=
    (continuousMultilinearCurryRightEquiv' ℝ q E F)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContDiff ℝ (k : ℕ∞ω) L :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E [×(q + 1)]→L[ℝ] F)
      (F := E [×q]→L[ℝ] (E →L[ℝ] F)) L
  have h := hL.comp_contDiffOn (hjets (q + 1))
  apply h.congr
  intro p _
  change _ = L (iteratedFDeriv ℝ (q + 1) (f p.1) p.2)
  rw [iteratedFDeriv_succ_eq_comp_right]
  exact ((continuousMultilinearCurryRightEquiv' ℝ q E F).apply_symm_apply _).symm

theorem contDiffOn_spatial_jets_prodMk
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {J : Set ℝ} {U : Set E} (hU : IsOpen U) (k : ℕ)
    (f : ℝ → E → F) (g : ℝ → E → G)
    (hf : ∀ t ∈ J, ContDiffOn ℝ ∞ (f t) U)
    (hg : ∀ t ∈ J, ContDiffOn ℝ ∞ (g t) U)
    (hfj : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E => iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U))
    (hgj : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E => iteratedFDeriv ℝ q (g p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E =>
        iteratedFDeriv ℝ q (fun x => (f p.1 x, g p.1 x)) p.2) (J ×ˢ U) := by
  intro q
  let L : ((E [×q]→L[ℝ] F) × (E [×q]→L[ℝ] G)) →L[ℝ]
      (E [×q]→L[ℝ] (F × G)) :=
    (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin q => E) F G)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.contDiff.comp_contDiffOn ((hfj q).prodMk (hgj q))
  apply h.congr
  intro p hp
  exact iteratedFDeriv_prodMk
    ((hf p.1 hp.1).contDiffAt (hU.mem_nhds hp.2))
    ((hg p.1 hp.1).contDiffAt (hU.mem_nhds hp.2))
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

theorem contDiffOn_spatial_jets_comp
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {J : Set ℝ} {U : Set E} {W : Set F}
    (hU : IsOpen U) (hW : IsOpen W) (k : ℕ)
    (f : ℝ → E → F) (Phi : F → G)
    (hf : ∀ t ∈ J, ContDiffOn ℝ ∞ (f t) U)
    (hPhi : ContDiffOn ℝ ∞ Phi W)
    (hmap : ∀ t ∈ J, MapsTo (f t) U W)
    (hjets : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E => iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E =>
        iteratedFDeriv ℝ q (fun x => Phi (f p.1 x)) p.2) (J ×ˢ U) := by
  intro q
  induction q generalizing F G with
  | zero =>
    let L : (E [×0]→L[ℝ] F) →L[ℝ] F :=
      (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
    have h0 : ContDiffOn ℝ k (fun p : ℝ × E => f p.1 p.2) (J ×ˢ U) :=
      L.contDiff.comp_contDiffOn (hjets 0)
    have hc : ContDiffOn ℝ k (fun p : ℝ × E => Phi (f p.1 p.2)) (J ×ˢ U) :=
      (hPhi.of_le (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp h0
        (fun p hp => hmap p.1 hp.1 hp.2)
    let L' : G →L[ℝ] (E [×0]→L[ℝ] G) :=
      (continuousMultilinearCurryFin0 ℝ E G).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L'.contDiff.comp_contDiffOn hc
  | succ q ih =>
    let H : ℝ → E → F × (E →L[ℝ] F) := fun t x => (f t x, fderiv ℝ (f t) x)
    let Psi : F × (E →L[ℝ] F) → E →L[ℝ] G :=
      fun p => (fderiv ℝ Phi p.1).comp p.2
    have hd (t : ℝ) (ht : t ∈ J) : ContDiffOn ℝ ∞ (fderiv ℝ (f t)) U :=
      (hf t ht).fderiv_of_isOpen hU (by simp)
    have hH (t : ℝ) (ht : t ∈ J) : ContDiffOn ℝ ∞ (H t) U :=
      (hf t ht).prodMk (hd t ht)
    have hHj : ∀ r : ℕ, ContDiffOn ℝ k
        (fun p : ℝ × E => iteratedFDeriv ℝ r (H p.1) p.2) (J ×ˢ U) :=
      contDiffOn_spatial_jets_prodMk hU k f (fun t => fderiv ℝ (f t)) hf hd hjets
        (contDiffOn_spatial_jets_fderiv k f hjets)
    have hPsi : ContDiffOn ℝ ∞ Psi (W ×ˢ (univ : Set (E →L[ℝ] F))) :=
      ((hPhi.fderiv_of_isOpen hW (by simp)).comp contDiffOn_fst
        (fun p hp => hp.1)).clm_comp contDiffOn_snd
    have hQ := ih (F := F × (E →L[ℝ] F)) (G := E →L[ℝ] G)
      (W := W ×ˢ (univ : Set (E →L[ℝ] F))) (hW := hW.prod isOpen_univ)
      (f := H) (Phi := Psi) hH hPsi (fun t ht x hx => ⟨hmap t ht hx, mem_univ _⟩) hHj
    let L : (E [×q]→L[ℝ] (E →L[ℝ] G)) →L[ℝ] (E [×(q + 1)]→L[ℝ] G) :=
      (continuousMultilinearCurryRightEquiv' ℝ q E G).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap
    have h := L.contDiff.comp_contDiffOn hQ
    apply h.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right]
    change L (iteratedFDeriv ℝ q (fderiv ℝ (fun x => Phi (f p.1 x))) p.2) =
      L (iteratedFDeriv ℝ q (fun x => Psi (H p.1 x)) p.2)
    apply congrArg L
    have heq : fderiv ℝ (fun x => Phi (f p.1 x)) =ᶠ[𝓝 p.2] fun x => Psi (H p.1 x) := by
      filter_upwards [hU.mem_nhds hp.2] with x hx
      exact (((hPhi.contDiffAt (hW.mem_nhds (hmap p.1 hp.1 hx))).differentiableAt
        (by simp)).hasFDerivAt.comp x
          (((hf p.1 hp.1).contDiffAt (hU.mem_nhds hx)).differentiableAt
            (by simp)).hasFDerivAt).fderiv
    exact (heq.iteratedFDeriv ℝ q).eq_of_nhds

theorem contDiffOn_spatial_jets_inverse
    {E P Q : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {J : Set ℝ} {U : Set E} (hU : IsOpen U) (k : ℕ)
    (A : ℝ → E → P →L[ℝ] Q)
    (hA : ∀ t ∈ J, ContDiffOn ℝ ∞ (A t) U)
    (hInv : ∀ t ∈ J, ∀ x ∈ U, (A t x).IsInvertible)
    (hjets : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E => iteratedFDeriv ℝ q (A p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × E =>
        iteratedFDeriv ℝ q (fun x => (A p.1 x).inverse) p.2) (J ×ˢ U) := by
  let W : Set (P →L[ℝ] Q) := range (fun e : P ≃L[ℝ] Q => (e : P →L[ℝ] Q))
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen
  have hinv : ContDiffOn ℝ ∞ (ContinuousLinearMap.inverse :
      (P →L[ℝ] Q) → (Q →L[ℝ] P)) W := by
    intro B hB
    exact (show B.IsInvertible from hB).contDiffAt_map_inverse.contDiffWithinAt
  exact contDiffOn_spatial_jets_comp hU hW k A ContinuousLinearMap.inverse hA hinv
    (fun t ht x hx => hInv t ht x hx) hjets

end FiniteSpatialJets

end PoincareConjecture.Proofs.M03
