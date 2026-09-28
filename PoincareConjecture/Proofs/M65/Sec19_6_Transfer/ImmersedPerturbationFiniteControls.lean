import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationBlockNeighborhood
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationCompact











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))



def loopSite (z : LoopAmbient) : (LoopCircle × LoopCircle) × ℝ :=
  ((ang (z 0), ang (z 1)), z 2)



theorem loopSite_open_quotient : IsOpenQuotientMap loopSite := by
  have hAng : IsOpenQuotientMap ang := by
    refine ⟨m65AngularCircle_surjective,
      Proofs.M58.contDiff_angularPoint.continuous.subtype_mk _, ?_⟩
    intro U hU
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [← m65AngularCircle_map_nhds x]
    exact image_mem_map (hU.mem_nhds hx)
  let A : LoopAmbient →L[ℝ] (ℝ × ℝ) × ℝ :=
    ((EuclideanSpace.proj 0).prod (EuclideanSpace.proj 1)).prod (EuclideanSpace.proj 2)
  have hinj : Function.Injective A := by
    intro z w h
    have h0 := congrArg (fun v : (ℝ × ℝ) × ℝ => v.1.1) h
    have h1 := congrArg (fun v : (ℝ × ℝ) × ℝ => v.1.2) h
    have h2 := congrArg (fun v : (ℝ × ℝ) × ℝ => v.2) h
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hsurj : Function.Surjective A := by
    rintro ⟨⟨x, y⟩, t⟩
    exact ⟨WithLp.toLp 2 ![x, y, t], rfl⟩
  let e : LoopAmbient ≃L[ℝ] (ℝ × ℝ) × ℝ := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ((hAng.prodMap hAng).prodMap IsOpenQuotientMap.id).comp
    e.toHomeomorph.isOpenQuotientMap

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {J : Set ℝ}

private theorem original_circle_continuous (C : M65SmoothFilledLoopFamily F J) (hJ : IsOpen J) :
    ContinuousOn (fun z : LoopCircle × ℝ => C.loops z.2 z.1) (univ ×ˢ J) := by
  let Gamma : ℝ → ℝ → C1FreeLoopSpace (M := M) := fun _ => C.loops
  have hGamma : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1) ((univ ×ˢ univ) ×ˢ J) :=
    (C.joint_smooth.of_le (by simp)).comp
      (contDiff_fst.fst.prodMk contDiff_snd).contMDiff.contMDiffOn
      (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hc := continuousOn_circle_family Gamma univ J isOpen_univ hJ hGamma
  exact hc.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨⟨mem_univ _, mem_univ (0 : ℝ)⟩, hz.2⟩)

variable [T2Space M] [CompactSpace M]

set_option maxHeartbeats 1000000 in





theorem exists_finite_regular_controls (C : M65SmoothFilledLoopFamily F J)
    (hJ : IsOpen J) (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ (k : ℕ) (d : Fin k → ℝ) (beta : Fin k → LoopPlane → ℝ)
        (Phi : Fin k → Fin 3 → M × ℝ → M) (q : Fin k → M)
        (U : Fin k → Set ((Fin 3 → ℝ) × LoopAmbient)),
      (∀ i, 0 < d i) ∧ (∀ i, ContDiff ℝ ∞ (beta i)) ∧
      (∀ i w, beta i w ∈ Icc (0 : ℝ) 1) ∧
      (∀ i j, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i j)
        (univ ×ˢ Ioo (-(d i)) (d i))) ∧
      (∀ i j y, Phi i j (y, 0) = y) ∧ (∀ i, IsOpen (U i)) ∧
      (∀ i w, w ∈ U i → w.2 2 ∈ J ∧
        periodicFreeLoop (C.loops (w.2 2)) (w.2 0) ∈ (chartAt LoopAmbient (q i)).source ∧
        periodicFreeLoop (C.loops (w.2 2)) (w.2 1) ∈ (chartAt LoopAmbient (q i)).source) ∧
      (∀ i, ContDiffOn ℝ 1 (doublePointEquation C (Phi i)
        (fun _ x => beta i (Proofs.M58.angularPoint x)) (List.finRange 3) (q i)) (U i)) ∧
      (∀ i w, w ∈ U i → Function.Bijective (fderiv ℝ (fun p =>
        doublePointEquation C (Phi i) (fun _ x => beta i (Proofs.M58.angularPoint x))
          (List.finRange 3) (q i) (p, w.2)) w.1)) ∧
      ∀ w : (LoopCircle × LoopCircle) × ℝ, w.2 ∈ K → rho ≤ dist w.1.1 w.1.2 →
        C.loops w.2 w.1.1 = C.loops w.2 w.1.2 →
          ∃ i z, (0, z) ∈ U i ∧ loopSite z = w := by
  classical
  let D : Set ((LoopCircle × LoopCircle) × ℝ) :=
    {w | w.2 ∈ K ∧ rho ≤ dist w.1.1 w.1.2 ∧ C.loops w.2 w.1.1 = C.loops w.2 w.1.2}
  have hD : IsCompact D := compact_separated_double_points (fun t x => C.loops t x) K hK
    ((original_circle_continuous C hJ).mono (prod_mono Subset.rfl hKJ)) rho
  have hlocal (w : D) :
      ∃ (z : LoopAmbient) (d : ℝ) (beta : LoopPlane → ℝ) (Phi : Fin 3 → M × ℝ → M)
          (q : M) (U : Set ((Fin 3 → ℝ) × LoopAmbient)),
        loopSite z = w.1 ∧ 0 < d ∧ ContDiff ℝ ∞ beta ∧
        (∀ v, beta v ∈ Icc (0 : ℝ) 1) ∧
        (∀ j, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi j)
          (univ ×ˢ Ioo (-d) d)) ∧ (∀ j y, Phi j (y, 0) = y) ∧
        IsOpen U ∧ (0, z) ∈ U ∧
        (∀ v ∈ U, v.2 2 ∈ J ∧
          periodicFreeLoop (C.loops (v.2 2)) (v.2 0) ∈ (chartAt LoopAmbient q).source ∧
          periodicFreeLoop (C.loops (v.2 2)) (v.2 1) ∈ (chartAt LoopAmbient q).source) ∧
        ContDiffOn ℝ 1 (doublePointEquation C Phi
          (fun _ x => beta (Proofs.M58.angularPoint x)) (List.finRange 3) q) U ∧
        ∀ v ∈ U, Function.Bijective (fderiv ℝ (fun p =>
          doublePointEquation C Phi (fun _ x => beta (Proofs.M58.angularPoint x))
            (List.finRange 3) q (p, v.2)) v.1) := by
    obtain ⟨z, hz⟩ := loopSite_open_quotient.surjective w.1
    have hx : ang (z 0) = w.1.1.1 := congrArg (fun v => v.1.1) hz
    have hy : ang (z 1) = w.1.1.2 := congrArg (fun v => v.1.2) hz
    have ht : z 2 = w.1.2 := congrArg Prod.snd hz
    have htJ : z 2 ∈ J := ht ▸ hKJ w.2.1
    have hxy : ang (z 0) ≠ ang (z 1) := by
      rw [hx, hy]
      intro h
      have hs := w.2.2.1
      rw [h, dist_self] at hs
      exact (not_le_of_gt hrho) hs
    have heq : periodicFreeLoop (C.loops (z 2)) (z 0) =
        periodicFreeLoop (C.loops (z 2)) (z 1) := by
      apply ((C.loops (z 2)).boundary (ang (z 0))).trans
      apply Eq.trans _ ((C.loops (z 2)).boundary (ang (z 1))).symm
      rw [hx, hy, ht]
      exact w.2.2.2
    obtain ⟨d, beta, Phi, U, hd, hbeta, hbound, _, _, hPhi, hzero, hU, hzU, hQU, hBU⟩ :=
      exists_doublePoint_regular_neighborhood C hJ z (ht ▸ hKJ w.2.1) hxy heq
    let q := periodicFreeLoop (C.loops (z 2)) (z 0)
    have hc (i : Fin 3) : ContinuousAt (fun v : LoopAmbient =>
        periodicFreeLoop (C.loops (v 2)) (v i)) z := by
      have hcoord : ContDiff ℝ ∞ (fun v : LoopAmbient => (v i, v 2)) :=
        (EuclideanSpace.proj i : LoopAmbient →L[ℝ] ℝ).contDiff.prodMk
          (EuclideanSpace.proj 2 : LoopAmbient →L[ℝ] ℝ).contDiff
      exact ((C.joint_smooth.contMDiffAt ((isOpen_univ.prod hJ).mem_nhds
        ⟨mem_univ _, ht ▸ hKJ w.2.1⟩)).comp z hcoord.contMDiff.contMDiffAt).continuousAt
    have hxq : periodicFreeLoop (C.loops (z 2)) (z 0) ∈ (chartAt LoopAmbient q).source :=
      mem_chart_source _ _
    have hyq : periodicFreeLoop (C.loops (z 2)) (z 1) ∈ (chartAt LoopAmbient q).source :=
      heq ▸ hxq
    have hnear : ∀ᶠ v : LoopAmbient in 𝓝 z, v 2 ∈ J ∧
        periodicFreeLoop (C.loops (v 2)) (v 0) ∈ (chartAt LoopAmbient q).source ∧
        periodicFreeLoop (C.loops (v 2)) (v 1) ∈ (chartAt LoopAmbient q).source := by
      filter_upwards
        [(EuclideanSpace.proj 2 : LoopAmbient →L[ℝ] ℝ).continuous.continuousAt.preimage_mem_nhds
          (hJ.mem_nhds htJ),
        (hc 0).preimage_mem_nhds ((chartAt LoopAmbient q).open_source.mem_nhds hxq),
        (hc 1).preimage_mem_nhds ((chartAt LoopAmbient q).open_source.mem_nhds hyq)]
        with v hv hxv hyv
      exact ⟨hv, hxv, hyv⟩
    obtain ⟨O, hO, hOo, hzO⟩ := _root_.mem_nhds_iff.mp hnear
    refine ⟨z, d, beta, Phi, q, U ∩ (univ ×ˢ O), hz, hd, hbeta, hbound, hPhi, hzero,
      hU.inter (isOpen_univ.prod hOo), ⟨hzU, mem_univ _, hzO⟩,
      fun v hv => hO hv.2.2, hQU.mono inter_subset_left, ?_⟩
    exact fun v hv => hBU v hv.1
  choose z d beta Phi q U hz hd hbeta hbound hPhi hzero hU hzU hsource hQU hBU using hlocal
  let O : D → Set ((LoopCircle × LoopCircle) × ℝ) :=
    fun i => loopSite '' {v | (0, v) ∈ U i}
  have hO (i : D) : IsOpen (O i) :=
    loopSite_open_quotient.isOpenMap _ ((hU i).preimage (continuous_const.prodMk continuous_id))
  have hcover : D ⊆ ⋃ i : D, O i := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, z ⟨w, hw⟩, hzU ⟨w, hw⟩, hz ⟨w, hw⟩⟩
  obtain ⟨L, hL⟩ := hD.elim_finite_subcover O hO hcover
  let e : Fin L.card ≃ L := L.equivFin.symm
  refine ⟨L.card, fun i => d (e i).1, fun i => beta (e i).1,
    fun i => Phi (e i).1, fun i => q (e i).1, fun i => U (e i).1,
    fun i => hd _, fun i => hbeta _, fun i => hbound _, fun i => hPhi _,
    fun i => hzero _, fun i => hU _, fun i => hsource _, fun i => hQU _, fun i => hBU _, ?_⟩
  intro w ht hs heq
  obtain ⟨i, hi, v, hv, hvi⟩ := mem_iUnion₂.mp (hL ⟨ht, hs, heq⟩)
  refine ⟨e.symm ⟨i, hi⟩, v, ?_, hvi⟩
  simpa only [e.apply_symm_apply, mem_ofPred_eq] using hv

end PoincareConjecture.M65Perturbation
