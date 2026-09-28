import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.End
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Slice
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import Mathlib.Geometry.Manifold.Algebra.Structures










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

private theorem positiveEnd_injOn (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) : InjOn C.cover (univ ×ˢ Ioi r) := by
  intro p hp q hq heq
  rcases (C.cover_fibers p q).mp heq with he | he
  · exact he.symm
  · have hh : q.2 = -p.2 := congrArg Prod.snd he
    have hp' : r < p.2 := hp.2
    have hq' : r < q.2 := hq.2
    linarith

noncomputable def positiveEndChart (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) : OpenPartialHomeomorph RoundCylinderSpace M :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((C.positiveEnd_injOn hr).toPartialEquiv C.cover (univ ×ˢ Ioi r))
    C.cover_local_diffeomorph.contMDiff.continuous.continuousOn
    C.cover_local_diffeomorph.isOpenMap (isOpen_univ.prod isOpen_Ioi)

@[simp] theorem positiveEndChart_apply (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) (p : RoundCylinderSpace) :
    C.positiveEndChart hr p = C.cover p := rfl

@[simp] theorem positiveEndChart_source (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) : (C.positiveEndChart hr).source = univ ×ˢ Ioi r := rfl

theorem positiveEndChart_target (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) : (C.positiveEndChart hr).target = (C.slabCore r)ᶜ := by
  rw [C.complement_slabCore hr]
  change C.cover '' (univ ×ˢ Ioi r) = _
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1, ⟨p.2, hp.2⟩), rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(p.1, p.2.1), ⟨mem_univ _, p.2.2⟩, rfl⟩

theorem positiveEndChart_inverse_smooth (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (C.positiveEndChart hr).symm (C.positiveEndChart hr).target := by
  intro x hx
  let e := C.positiveEndChart hr
  let h := C.cover_local_diffeomorph (e.symm x)
  have he : C.cover (e.symm x) = x := e.right_inv hx
  have hc : ContinuousAt e.symm x :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hx)
  have hnear : ∀ᶠ y in 𝓝 x, e.symm y ∈ h.localInverse.target :=
    hc.preimage_mem_nhds (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)
  have hsmooth : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ h.localInverse x := by
    simpa only [he] using h.localInverse_contMDiffAt
  apply ContMDiffAt.contMDiffWithinAt
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hx, hnear] with y hy hlocal
  change e.symm y = h.localInverse y
  have hright := h.localInverse_left_inv hlocal
  change h.localInverse (e (e.symm y)) = e.symm y at hright
  rw [e.right_inv hy] at hright
  exact hright.symm

private def endLine (r s : ℝ) : ℝ := r + s / (1 - s)

private def endLineInv (r h : ℝ) : ℝ := (h - r) / (1 + (h - r))

private theorem endLine_mem (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    endLine r s ∈ Ioi r := by
  dsimp [endLine]
  exact lt_add_of_pos_right r (div_pos hs.1 (sub_pos.mpr hs.2))

private theorem endLineInv_mem {r h : ℝ} (hh : r < h) :
    endLineInv r h ∈ Ioo (0 : ℝ) 1 := by
  have hd : 0 < 1 + (h - r) := by linarith
  exact ⟨div_pos (sub_pos.mpr hh) hd, (div_lt_one hd).mpr (by linarith)⟩

private theorem endLineInv_endLine (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    endLineInv r (endLine r s) = s := by
  have hd : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs.2)
  dsimp [endLineInv, endLine]
  field_simp
  ring

private theorem endLine_endLineInv {r h : ℝ} (hh : r < h) :
    endLine r (endLineInv r h) = h := by
  have hd : 1 + (h - r) ≠ 0 := by linarith
  dsimp [endLine, endLineInv]
  field_simp
  ring

private def endLineHomeomorph (r : ℝ) : Ioo (0 : ℝ) 1 ≃ₜ Ioi r where
  toFun s := ⟨endLine r s.1, endLine_mem r s.2⟩
  invFun h := ⟨endLineInv r h.1, endLineInv_mem h.2⟩
  left_inv s := Subtype.ext (endLineInv_endLine r s.2)
  right_inv h := Subtype.ext (endLine_endLineInv h.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_subtype_val.div
      (continuous_const.sub continuous_subtype_val) (fun s => by linarith [s.2.2]))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).div
      (continuous_const.add (continuous_subtype_val.sub continuous_const))
      (fun h => by linarith [show r < h.1 from h.2])

private theorem endLine_contDiffAt (r : ℝ) {s : ℝ} (hs : s < 1) :
    ContDiffAt ℝ ∞ (endLine r) s :=
  contDiffAt_const.add (contDiffAt_id.div (contDiffAt_const.sub contDiffAt_id)
    (by linarith))

private theorem endLineInv_contDiffAt {r h : ℝ} (hh : r < h) :
    ContDiffAt ℝ ∞ (endLineInv r) h :=
  (contDiffAt_id.sub contDiffAt_const).div
    (contDiffAt_const.add (contDiffAt_id.sub contDiffAt_const)) (by linarith)

noncomputable def positiveEndCylinder (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) : OpenCylinderModel (C.slabCore r)ᶜ := by
  let e := C.positiveEndChart hr
  let h : (UnitTwoSphere × Ioi r) ≃ₜ (univ ×ˢ Ioi r : Set RoundCylinderSpace) :=
    (((Homeomorph.Set.univ UnitTwoSphere).symm).prodCongr
      (Homeomorph.refl (Ioi r))).trans (Homeomorph.Set.prod univ (Ioi r)).symm
  refine {
    homeomorph := (((Homeomorph.refl UnitTwoSphere).prodCongr
      (endLineHomeomorph r)).trans h).trans
        (e.toHomeomorphSourceTarget.trans (Homeomorph.setCongr (C.positiveEndChart_target hr)))
    coordinate := fun z => C.cover (z.1, endLine r z.2)
    coordinate_eq := fun z => rfl
    coordinate_smooth := ?_
    inverse := fun x => ((e.symm x).1, endLineInv r (e.symm x).2)
    inverse_mem := ?_
    left_inverse := ?_
    right_inverse := ?_
    inverse_smooth := ?_ }
  · intro z hz
    exact (C.cover_local_diffeomorph.contMDiff.contMDiffAt.comp z
      (contMDiffAt_fst.prodMk
        ((endLine_contDiffAt r hz.2.2).contMDiffAt.comp z contMDiffAt_snd))).contMDiffWithinAt
  · intro x hx
    have hm := e.map_target ((C.positiveEndChart_target hr).symm ▸ hx)
    exact ⟨mem_univ _, endLineInv_mem hm.2⟩
  · intro z hz
    change ((e.symm (e (z.1, endLine r z.2))).1,
      endLineInv r (e.symm (e (z.1, endLine r z.2))).2) = z
    rw [e.left_inv (show (z.1, endLine r z.2) ∈ e.source from
      ⟨mem_univ _, endLine_mem r hz.2⟩)]
    exact Prod.ext rfl (endLineInv_endLine r hz.2)
  · intro x hx
    have hm := e.map_target ((C.positiveEndChart_target hr).symm ▸ hx)
    change C.cover ((e.symm x).1, endLine r (endLineInv r (e.symm x).2)) = x
    rw [endLine_endLineInv hm.2]
    exact e.right_inv ((C.positiveEndChart_target hr).symm ▸ hx)
  · intro x hx
    have hx' : x ∈ e.target := (C.positiveEndChart_target hr).symm ▸ hx
    have hm := e.map_target hx'
    have he := (C.positiveEndChart_inverse_smooth hr).contMDiffAt (e.open_target.mem_nhds hx')
    exact ((contMDiffAt_fst.comp x he).prodMk
      ((endLineInv_contDiffAt hm.2).contMDiffAt.comp x
        (contMDiffAt_snd.comp x he))).contMDiffWithinAt

@[simp] theorem positiveEndCylinder_coordinate (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) (z : RoundCylinderSpace) :
    (C.positiveEndCylinder hr).coordinate z = C.cover (z.1, r + z.2 / (1 - z.2)) := rfl

theorem positiveEndCylinder_middleSphere (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) :
    (C.positiveEndCylinder hr).middleSphere = range (fun q => C.cover (q, r + 1)) := by
  ext x
  constructor
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, he⟩
    have hs' : s = 1 / 2 := hs
    subst s
    exact ⟨q, by norm_num at he ⊢; exact he⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, by norm_num⟩

private theorem endLine_lt_iff (r : ℝ) {s a : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) :
    endLine r s < endLine r a ↔ s < a := by
  dsimp only [endLine]
  rw [add_lt_add_iff_left, div_lt_div_iff₀ (sub_pos.mpr hs.2) (sub_pos.mpr ha.2)]
  constructor <;> intro h <;> nlinarith

theorem positiveEndCylinder_tail_false (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (C.positiveEndCylinder hr).tail false a =
      C.cover '' (univ ×ˢ Ioo r (r + a / (1 - a))) := by
  change (fun z => C.cover (z.1, endLine r z.2)) '' (univ ×ˢ Ioo 0 a) =
    C.cover '' (univ ×ˢ Ioo r (endLine r a))
  ext x
  constructor
  · rintro ⟨p, hp, he⟩
    have hs : p.2 ∈ Ioo (0 : ℝ) 1 := ⟨hp.2.1, hp.2.2.trans ha.2⟩
    exact ⟨(p.1, endLine r p.2),
      ⟨mem_univ _, endLine_mem r hs, (endLine_lt_iff r hs ha).mpr hp.2.2⟩, he⟩
  · rintro ⟨p, hp, he⟩
    have hs := endLineInv_mem hp.2.1
    have hlt : endLineInv r p.2 < a := (endLine_lt_iff r hs ha).mp (by
      rw [endLine_endLineInv hp.2.1]
      exact hp.2.2)
    refine ⟨(p.1, endLineInv r p.2), ⟨mem_univ _, hs.1, hlt⟩, ?_⟩
    dsimp only
    rw [endLine_endLineInv hp.2.1]
    exact he

theorem positiveEndCylinder_tail_true (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (C.positiveEndCylinder hr).tail true a =
      C.cover '' (univ ×ˢ Ioi (r + a / (1 - a))) := by
  change (fun z => C.cover (z.1, endLine r z.2)) '' (univ ×ˢ Ioo a 1) =
    C.cover '' (univ ×ˢ Ioi (endLine r a))
  ext x
  constructor
  · rintro ⟨p, hp, he⟩
    have hs : p.2 ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hp.2.1, hp.2.2⟩
    exact ⟨(p.1, endLine r p.2),
      ⟨mem_univ _, (endLine_lt_iff r ha hs).mpr hp.2.1⟩, he⟩
  · rintro ⟨p, hp, he⟩
    have hh : r < p.2 := (endLine_mem r ha).trans hp.2
    have hs := endLineInv_mem hh
    have hlt : a < endLineInv r p.2 := (endLine_lt_iff r ha hs).mp (by
      rw [endLine_endLineInv hh]
      exact hp.2)
    refine ⟨(p.1, endLineInv r p.2), ⟨mem_univ _, hlt, hs.2⟩, ?_⟩
    dsimp only
    rw [endLine_endLineInv hh]
    exact he

theorem positiveEndSlice_isSmoothEmbedding (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) {h : ℝ} (hh : r < h) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => C.cover (q, h)) :=
  (C.positiveEndChart hr).isSmoothEmbedding_slice
    C.cover_local_diffeomorph.contMDiff.contMDiffOn
    (C.positiveEndChart_inverse_smooth hr) (RiemannianMetric.lineModelEquiv 2)
    h (fun _ => ⟨mem_univ _, hh⟩)

theorem positiveEnd_slices_isotopic (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) {h₀ h₁ : ℝ} (h₀r : r < h₀) (h₁r : r < h₁) :
    SmoothSphereIsotopicIn (C.slabCore r)ᶜ
      (range (fun q => C.cover (q, h₀))) (range (fun q => C.cover (q, h₁))) := by
  let height := fun z : ℝ × UnitTwoSphere => (1 - z.1) * h₀ + z.1 * h₁
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ height :=
    ((contMDiff_const.sub contMDiff_fst).mul contMDiff_const).add
      (contMDiff_fst.mul contMDiff_const)
  have hheight (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      r < (1 - t) * h₀ + t * h₁ :=
    convex_Ioi r h₀r h₁r (sub_nonneg.mpr ht.2) ht.1 (by ring)
  refine ⟨fun z => C.cover (z.2, height z),
    (C.cover_local_diffeomorph.contMDiff.comp (contMDiff_snd.prodMk hsmooth)).contMDiffOn,
    ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨C.positiveEndSlice_isSmoothEmbedding hr (hheight t ht), ?_⟩
    rintro x ⟨q, rfl⟩
    rw [← C.positiveEndChart_target hr]
    exact (C.positiveEndChart hr).map_source ⟨mem_univ _, hheight t ht⟩
  · simp only [height, sub_zero, one_mul, zero_mul, add_zero]
  · simp only [height, sub_self, zero_mul, one_mul, zero_add]

theorem positiveEndSlice_isotopic_middleSphere
    (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) {h : ℝ} (hh : r < h) :
    SmoothSphereIsotopicIn (C.slabCore r)ᶜ (range (fun q => C.cover (q, h)))
      (C.positiveEndCylinder hr).middleSphere := by
  rw [C.positiveEndCylinder_middleSphere hr]
  exact C.positiveEnd_slices_isotopic hr hh (by linarith)

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
