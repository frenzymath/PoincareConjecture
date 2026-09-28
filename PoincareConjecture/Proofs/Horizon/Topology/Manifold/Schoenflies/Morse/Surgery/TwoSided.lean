import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.OutwardCap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.ParallelCuts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks.CuttingCharts



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private theorem projection_mem_transported_cap
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {y : E3} (hy : y ∈
      Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)})) :
    (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 := by
  rcases hy with ⟨z, ⟨p, _, rfl⟩, rfl⟩
  rw [Poincare.Geometry.Euclidean.projection_liftPlaneDiffeomorph]
  exact mem_image_of_mem A (mem_closedBall_zero_iff.mpr
    (norm_boundedCylinder_projection_le v hv p))




theorem exists_two_sided_surgery_of_cylindrical_tube
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (hcylinder : ∀ p t, t ∈ Ioo (-ε) ε ->
      f (T (p, t)) = (c + t) • v + (γ p : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => T (p, 0))) :
    ∃ a : Real, 0 < a ∧ a < ε / 4 ∧ ∃ s : Real, ∃ hs : 0 < s,
      s < a / 8 ∧ ∃ eMinus ePlus : OpenPartialHomeomorph E2 S2,
        closedBall 0 1 ⊆ eMinus.source ∧ closedBall 0 1 ⊆ ePlus.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus eMinus.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus.symm eMinus.target ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus ePlus.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus.symm ePlus.target ∧
        Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1) ∧
        eMinus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, -a)) ∧
        ePlus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, a)) ∧
        eMinus '' closedBall 0 1 ∪ T '' (univ ×ˢ Icc (-a) a) ∪
          ePlus '' closedBall 0 1 = univ ∧
        T '' (univ ×ˢ Icc (-a) a) =
          (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ ∧
        ∃ dMinus dPlus : OpenPartialHomeomorph E2 S2,
          closedBall 0 1 ⊆ dMinus.source ∧ closedBall 0 1 ⊆ dPlus.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ dMinus dMinus.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ dMinus.symm dMinus.target ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ dPlus dPlus.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ dPlus.symm dPlus.target ∧
          dMinus '' closedBall 0 1 = (eMinus '' ball 0 1)ᶜ ∧
          dMinus '' ball 0 1 = (eMinus '' closedBall 0 1)ᶜ ∧
          dPlus '' closedBall 0 1 = (ePlus '' ball 0 1)ᶜ ∧
          dPlus '' ball 0 1 = (ePlus '' closedBall 0 1)ᶜ ∧
          ∃ gMinus gPlus : E2 -> E3,
            ContDiff Real ∞ gMinus ∧ ContDiff Real ∞ gPlus ∧
            Injective gMinus ∧ Injective gPlus ∧
            (∀ x, Injective (fderiv Real gMinus x)) ∧
            (∀ x, Injective (fderiv Real gPlus x)) ∧
            (∀ x, |inner Real v (gMinus x) - (c - a)| < a / 2) ∧
            (∀ x, |inner Real v (gPlus x) - (c + a)| < a / 2) ∧
            gMinus '' closedBall (0 : E2) 1 =
              Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv (c - a) s hs.ne' A ''
                ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                  {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
            gPlus '' closedBall (0 : E2) 1 =
              Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv (c + a) (-s)
                (neg_ne_zero.mpr hs.ne') A ''
                ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                  {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
            ∃ fMinus fPlus : S2 -> E3,
              _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fMinus ∧
              _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fPlus ∧
              Disjoint (range fMinus) (range fPlus) ∧
              (∀ x ∈ closedBall 0 1, fMinus (dMinus x) = gMinus x) ∧
              (∀ x ∈ closedBall 0 1, fPlus (dPlus x) = gPlus x) ∧
              (∀ y ∈ eMinus '' closedBall 0 1, fMinus y = f y) ∧
              (∀ y ∈ ePlus '' closedBall 0 1, fPlus y = f y) ∧
              range fMinus = gMinus '' closedBall 0 1 ∪ f '' (eMinus '' closedBall 0 1) ∧
              range fPlus = gPlus '' closedBall 0 1 ∪ f '' (ePlus '' closedBall 0 1) ∧
              (∀ t ∈ Icc (-(2 * a)) (2 * a),
                ((fun x : Hemisphere.Plane v => (c + t) • v + (A x : E3)) ''
                  closedBall 0 1) ∩ range f = f '' range (fun q : S1 => T (q, t))) := by
  obtain ⟨δ, hδ, hδε, hparallel⟩ := exists_parallel_cutting_disks
    hf.contMDiff.continuous hf.isEmbedding.injective hv c hε T hsource
      γ hcylinder A hboundary hintersection
  obtain ⟨U, hUs, hU, hUi, hUraw⟩ := exists_reparametrized_sphere_tube
    T hT hTi hsource 0 1 one_ne_zero (r := δ) hδ (by simpa using hδε)
  have hUeq (p : S1) (t : Real) : U (p, t) = T (p, t) := by
    simpa using hUraw p t
  obtain ⟨a, ha, haδ, ha1, d, hd, hdi, hwide, q, hmatch,
    eMinus, ePlus, heMs, hePs, heM, heMi, heP, hePi, heMc, heMb,
    hePc, hePb, heMboundary, hePboundary, heDis, heCover, heSlab⟩ :=
    exists_parallel_disks_of_sphere_tube hδ U hU hUi hUs
  have haε : a < ε / 4 := by linarith
  have haδ' : a < δ := by linarith
  have hhalf : 0 < a / 2 := by positivity
  obtain ⟨eInner, eOuter, hIs, hOs, hI, hIi, hO, hOi, hIc, hIb, hOc, hOb,
    TPlus, TMinus, hTPs, hTMs, hTP, hTPi, hTM, hTMi,
    hTPeq, hTMeq, hTPboundary, hTMboundary, hTPin, hTMin⟩ :=
    exists_parallel_cutting_charts ha haδ ha1 U hU hUi hUs d hd hdi hwide q hmatch
  have hPcircle (p : S1) (t : Real) (ht : t ∈ Ioo (-(a / 2)) (a / 2)) :
      f (TPlus (p, t)) = (c + a + t) • v + (γ p : E3) := by
    rw [hTPeq, hUeq, hcylinder p (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 2
    ring
  have hMcircle (p : S1) (t : Real) (ht : t ∈ Ioo (-(a / 2)) (a / 2)) :
      f (TMinus (p, t)) = (c - a - t) • v + (γ p : E3) := by
    rw [hTMeq, hUeq, hcylinder p (-a - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    congr 2
    ring
  have hPinter :
      ((fun x : Hemisphere.Plane v => (c + a) • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => TPlus (p, 0)) := by
    simpa only [hTPeq, hUeq, add_zero] using hparallel a ⟨by linarith, haδ'.le⟩
  have hMinter :
      ((fun x : Hemisphere.Plane v => (c - a) • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => TMinus (p, 0)) := by
    simpa only [hTMeq, hUeq, sub_zero, sub_eq_add_neg, neg_zero, add_zero] using
      hparallel (-a) ⟨by linarith, by linarith⟩
  obtain ⟨δP, hδP, hcapP⟩ :=
    exists_capped_sphere_of_cylindrical_tube_with_disk_and_range_for_small_scale
      hf hv (c + a) hhalf hhalf TPlus hTP hTPi hTPs γ hγ hPcircle
      A hboundary hPinter eInner hIs hI hIi hTPboundary hTPin
  obtain ⟨δM, hδM, hcapM⟩ :=
    exists_outward_capped_sphere_of_cylindrical_tube_with_disk_and_range_for_small_scale
      hf hv (c - a) hhalf hhalf TMinus hTM hTMi hTMs γ hγ hMcircle
      A hboundary hMinter eOuter hOs hO hOi hTMboundary hTMin
  let s := min (min δM δP) (a / 8) / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsM : s < δM := by
    dsimp [s]
    linarith [min_le_left (min δM δP) (a / 8), min_le_left δM δP]
  have hsP : s < δP := by
    dsimp [s]
    linarith [min_le_left (min δM δP) (a / 8), min_le_right δM δP]
  have hsa : s < a / 8 := by
    dsimp [s]
    linarith [min_le_right (min δM δP) (a / 8)]
  obtain ⟨dPlus, hdP, hdPi, hdPs, hdPc, hdPb, _, _, _,
    gPlus, hgP, hgiP, hgdP, _, _, hgwP, _, _, hgrP, fPlus, hfP,
    hfPcap, hfPoff, hfPrange⟩ := hcapP (-s) (by linarith) (by linarith)
  obtain ⟨dMinus, hdM, hdMi, hdMs, hdMc, hdMb, _, _, _,
    gMinus, hgM, hgiM, hgdM, _, _, hgwM, _, _, hgrM, fMinus, hfM,
    hfMcap, hfMoff, hfMrange⟩ := hcapM s hsM hs
  have hdmclosed : dMinus '' closedBall 0 1 = (eMinus '' ball 0 1)ᶜ := by
    rw [hdMc, hOc, heMb]
  have hdmopen : dMinus '' ball 0 1 = (eMinus '' closedBall 0 1)ᶜ := by
    rw [hdMb, hOb, heMc]
  have hdpclosed : dPlus '' closedBall 0 1 = (ePlus '' ball 0 1)ᶜ := by
    rw [hdPc, hIc, hePb, compl_compl]
  have hdpopen : dPlus '' ball 0 1 = (ePlus '' closedBall 0 1)ᶜ := by
    rw [hdPb, hIb, hePc, compl_compl]
  have hclear (y : E3)
      (hy : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1)
      (hyt : |inner Real v y - c| ≤ 2 * a)
      (p : S2) (hpy : f p = y) :
      ∃ w : S1, p = U (w, inner Real v y - c) := by
    let t := inner Real v y - c
    have ht : t ∈ Icc (-δ) δ := by
      have h := abs_le.mp hyt
      exact ⟨by dsimp [t]; linarith [h.1], by dsimp [t]; linarith [h.2]⟩
    obtain ⟨z, hz, hproj⟩ := hy
    have hyplane : y ∈
        (fun x : Hemisphere.Plane v => (c + t) • v + (A x : E3)) '' closedBall 0 1 := by
      refine ⟨z, hz, ?_⟩
      have heq := (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply y
      change inner Real v y • v +
        ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at heq
      rw [← hproj] at heq
      rw [show c + t = inner Real v y by dsimp [t]; ring]
      exact heq
    obtain ⟨p', ⟨w, rfl⟩, hw⟩ := (hparallel t ht) ▸
      (show y ∈ ((fun x : Hemisphere.Plane v => (c + t) • v + (A x : E3)) ''
        closedBall 0 1) ∩ range f from ⟨hyplane, ⟨p, hpy⟩⟩)
    refine ⟨w, ?_⟩
    rw [hUeq]
    exact hf.isEmbedding.injective (hpy.trans hw.symm)
  have hcapMaway : Disjoint (gMinus '' closedBall 0 1) (f '' (ePlus '' closedBall 0 1)) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨p, hp, hpx⟩
    have hwidth := abs_lt.mp (hgwM x)
    have ht : |inner Real v (gMinus x) - c| ≤ 2 * a := by
      apply abs_le.mpr
      constructor <;> linarith
    obtain ⟨w, hpw⟩ := hclear (gMinus x)
      (projection_mem_transported_cap hv (c - a) s hs.ne' A
        (hgrM ▸ mem_image_of_mem gMinus hx)) ht p hpx
    rw [hePc] at hp
    apply hp
    let t := inner Real v (gMinus x) - c
    have ht2 : |t| ≤ 2 * a := ht
    have hpos : 0 < 1 + t := by
      have := (abs_le.mp ht2).1
      linarith
    refine ⟨(1 + t) • ((q.symm w : S1) : E2), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
        norm_eq_of_mem_sphere, mul_one]
      dsimp [t]
      linarith
    · rw [hmatch _ t ht2, q.apply_symm_apply]
      exact hpw.symm
  have hcapPaway : Disjoint (gPlus '' closedBall 0 1) (f '' (eMinus '' closedBall 0 1)) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨p, hp, hpx⟩
    have hwidth := abs_lt.mp (hgwP x)
    have ht : |inner Real v (gPlus x) - c| ≤ 2 * a := by
      apply abs_le.mpr
      constructor <;> linarith
    obtain ⟨w, hpw⟩ := hclear (gPlus x)
      (projection_mem_transported_cap hv (c + a) (-s) (neg_ne_zero.mpr hs.ne') A
        (hgrP ▸ mem_image_of_mem gPlus hx)) ht p hpx
    rw [heMc] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    let t := inner Real v (gPlus x) - c
    have ht2 : |t| ≤ 2 * a := ht
    have hpos : 0 < 1 + t := by
      have := (abs_le.mp ht2).1
      linarith
    have hnorm : ‖(1 + t) • ((q.symm w : S1) : E2)‖ = 1 + t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, norm_eq_of_mem_sphere, mul_one]
    have hzs : z ∈ d.source := hwide
      ((closedBall_subset_closedBall (by linarith)) hz)
    have hrs : (1 + t) • ((q.symm w : S1) : E2) ∈ d.source := hwide
      (mem_closedBall_zero_iff.mpr (by rw [hnorm]; linarith [(abs_le.mp ht2).2]))
    have hzrad : z = (1 + t) • ((q.symm w : S1) : E2) := d.injOn hzs hrs (by
      rw [hmatch _ t ht2, q.apply_symm_apply]
      exact hzp.trans hpw)
    have hzbound := mem_closedBall_zero_iff.mp hz
    rw [hzrad, hnorm] at hzbound
    dsimp [t] at hzbound
    linarith
  have hcapsDis : Disjoint (gMinus '' closedBall 0 1) (gPlus '' closedBall 0 1) := by
    apply disjoint_left.mpr
    rintro y ⟨x, _, rfl⟩ ⟨z, _, hz⟩
    have hm := abs_lt.mp (hgwM x)
    have hp := abs_lt.mp (hgwP z)
    rw [hz] at hp
    linarith
  have hretainedDis : Disjoint (f '' (eMinus '' closedBall 0 1))
      (f '' (ePlus '' closedBall 0 1)) :=
    heDis.image hf.isEmbedding.injective.injOn (subset_univ _) (subset_univ _)
  have hbothDis : Disjoint (range fMinus) (range fPlus) := by
    rw [hfMrange, hfPrange, hdmopen, hdpopen, compl_compl, compl_compl]
    exact disjoint_union_left.mpr
      ⟨disjoint_union_right.mpr ⟨hcapsDis, hcapMaway⟩,
        disjoint_union_right.mpr ⟨hcapPaway.symm, hretainedDis⟩⟩
  have hUslab : U '' (univ ×ˢ Icc (-a) a) = T '' (univ ×ˢ Icc (-a) a) := by
    apply image_congr
    rintro ⟨p, t⟩ _
    exact hUeq p t
  refine ⟨a, ha, haε, s, hs, hsa, eMinus, ePlus, heMs, hePs,
    heM, heMi, heP, hePi, heDis, ?_, ?_, ?_, ?_,
    dMinus, dPlus, hdMs, hdPs, hdM, hdMi, hdP, hdPi,
    hdmclosed, hdmopen, hdpclosed, hdpopen, gMinus, gPlus, hgM, hgP,
    hgiM, hgiP, hgdM, hgdP, hgwM, hgwP, hgrM, hgrP,
    fMinus, fPlus, hfM, hfP, hbothDis, hfMcap, hfPcap, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hUeq] using heMboundary
  · simpa only [hUeq] using hePboundary
  · simpa only [hUslab] using heCover
  · simpa only [hUslab] using heSlab
  · intro y hy
    exact hfMoff y (by simpa only [hdmopen, mem_compl_iff, not_not] using hy)
  · intro y hy
    exact hfPoff y (by simpa only [hdpopen, mem_compl_iff, not_not] using hy)
  · simpa only [hdmopen, compl_compl] using hfMrange
  · simpa only [hdpopen, compl_compl] using hfPrange
  · intro t ht
    exact hparallel t ⟨by linarith [ht.1], by linarith [ht.2]⟩

end Poincare.Manifold.Schoenflies
