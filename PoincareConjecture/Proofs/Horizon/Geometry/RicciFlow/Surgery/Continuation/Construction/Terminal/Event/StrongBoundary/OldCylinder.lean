import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Extension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

def GeneralizedFlowCylinder.restrictTime
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {a q : ℝ} {J K : Set ℝ} {U : Set C.carrier}
    (d : GeneralizedFlowCylinder F C a q J U) (hK : K ⊆ J) :
    GeneralizedFlowCylinder F C a q K U where
  scale_pos := d.scale_pos
  forward s hs := d.forward s (hK hs)
  inverse s hs := d.inverse s (hK hs)
  forward_smooth s hs := d.forward_smooth s (hK hs)
  inverse_smooth s hs := d.inverse_smooth s (hK hs)
  left_inverse s hs := d.left_inverse s (hK hs)
  right_inverse s hs := d.right_inverse s (hK hs)
  embedding := d.embedding.comp ((IsEmbedding.inclusion hK).prodMap IsEmbedding.id)
  vertical_compatibility s hs x hx := by
    obtain ⟨b, y, δ, hδ, hworld⟩ := d.vertical_compatibility s (hK hs) x hx
    exact ⟨b, y, δ, hδ, fun t ht hdist => hworld t (hK ht) hdist⟩

namespace GeneralizedFlowExtension

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ} (E : GeneralizedFlowExtension F T)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (d : GeneralizedFlowCylinder E.extended C a q J U)
  (htime : ∀ s ∈ J, a + s / q ∈ F.interval)

theorem inverseCylinder_vertical (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U) :
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' hs', |s' - s| < δ → ∃ hb : a + s' / q ∈ (F.box b).interval,
        E.inverse (a + s' / q) (htime s' hs') (d.forward s' hs' x) =
          (F.box b).forward (a + s' / q) hb y := by
  obtain ⟨b, hb, y, hby⟩ := F.box_covers (a + s / q)
    (E.inverse (a + s / q) (htime s hs) (d.forward s hs x))
  obtain ⟨c, z, δ, hδ, hworld⟩ := E.vertical_compatibility b (a + s / q) hb y
  obtain ⟨k, w, r, hr, hcurve⟩ := d.vertical_compatibility s hs x hx
  obtain ⟨hc, hcz⟩ := hworld (a + s / q) hb (by simpa using hδ)
  obtain ⟨hk, hkw⟩ := hcurve s hs (by simpa using hr)
  have hbase : (E.extended.box c).forward (a + s / q) hc z =
      (E.extended.box k).forward (a + s / q) hk w := by
    rw [E.spacetime_slices _ (htime s hs) _] at hcz
    have he := eq_of_heq (Sigma.mk.inj hcz).2
    rw [hby, E.right_inverse] at he
    exact he.symm.trans hkw
  obtain ⟨O, hO, hbox⟩ := (F.box b).relatively_open
  have hsO : a + s / q ∈ O := (hbox ▸ hb).2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (a + s / q) hsO
  refine ⟨b, y, min r (min δ ε * q), lt_min hr (mul_pos (lt_min hδ hε) d.scale_pos), ?_⟩
  intro s' hs' hdist
  have hphysical : |(a + s' / q) - (a + s / q)| < min δ ε := by
    rw [show (a + s' / q) - (a + s / q) = (s' - s) / q by ring,
      abs_div, abs_of_pos d.scale_pos]
    exact (div_lt_iff₀ d.scale_pos).mpr (hdist.trans_le (min_le_right _ _))
  have hb' : a + s' / q ∈ (F.box b).interval := by
    rw [hbox]
    exact ⟨htime s' hs', hball (by
      simpa only [Metric.mem_ball, Real.dist_eq] using hphysical.trans_le (min_le_right _ _))⟩
  obtain ⟨hc', hcz'⟩ := hworld (a + s' / q) hb'
    (hphysical.trans_le (min_le_left _ _))
  obtain ⟨hk', hkw'⟩ := hcurve s' hs' (hdist.trans_le (min_le_left _ _))
  have hcw := E.extended.vertical_compatibility c k (a + s / q) hc hk z w hbase
    (a + s' / q) hc' hk'
  rw [E.spacetime_slices _ (htime s' hs') _] at hcz'
  have he : E.forward (a + s' / q) (htime s' hs')
      ((F.box b).forward (a + s' / q) hb' y) = d.forward s' hs' x :=
    (eq_of_heq (Sigma.mk.inj hcz').2).trans (hcw.trans hkw'.symm)
  refine ⟨hb', ?_⟩
  rw [← he, E.left_inverse]

def pullCylinder : GeneralizedFlowCylinder F C a q J U where
  scale_pos := d.scale_pos
  forward s hs := E.inverse (a + s / q) (htime s hs) ∘ d.forward s hs
  inverse s hs := d.inverse s hs ∘ E.forward (a + s / q) (htime s hs)
  forward_smooth s hs := (E.inverse_smooth _ _).comp_contMDiffOn (d.forward_smooth s hs)
  inverse_smooth s hs := by
    apply (d.inverse_smooth s hs).comp (E.forward_smooth _ _).contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, (E.right_inverse _ _ _).symm⟩
  left_inverse s hs x hx := by
    dsimp only [Function.comp_apply]
    rw [E.right_inverse, d.left_inverse s hs hx]
  right_inverse s hs y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [E.right_inverse, d.left_inverse s hs hx]
  embedding := by
    apply E.spacetime_openEmbedding.isEmbedding.of_comp_iff.mp
    convert d.embedding using 1
    funext p
    simp only [Function.comp_apply, E.spacetime_slices _ (htime p.1.val p.1.property) _]
    exact congrArg (Sigma.mk (a + p.1.val / q))
      (E.right_inverse _ (htime p.1.val p.1.property) _)
  vertical_compatibility := E.inverseCylinder_vertical d htime

@[simp] theorem pullCylinder_forward (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (E.pullCylinder d htime).forward s hs x =
      E.inverse (a + s / q) (htime s hs) (d.forward s hs x) := rfl

theorem pullCylinder_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (E.pullCylinder d htime).pullbackInner s hs x v w = d.pullbackInner s hs x v w := by
  let c := E.pullCylinder d htime
  have hC : Nonempty C.carrier := ⟨x⟩
  have heq : (E.pushCylinder c hC).forward s hs = d.forward s hs := by
    funext y
    exact E.right_inverse _ _ _
  calc
    c.pullbackInner s hs x v w = (E.pushCylinder c hC).pullbackInner s hs x v w :=
      (E.pushCylinder_pullbackInner c hC hU s hs x hx v w).symm
    _ = d.pullbackInner s hs x v w := by
      exact congrArg (fun f : C.carrier → (E.extended.slice (a + s / q)).carrier =>
        q * (E.extended.metric (a + s / q)).inner (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)) heq

end GeneralizedFlowExtension

end PoincareConjecture
