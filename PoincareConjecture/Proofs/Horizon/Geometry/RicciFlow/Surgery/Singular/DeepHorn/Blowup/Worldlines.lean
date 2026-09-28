import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Worldlines.Intervals
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Worldlines.Uniqueness
import Mathlib.Order.Zorn
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.DeepHorn

private theorem directed_intervals_local {α : Type*} (I : α → Set ℝ)
    (hI : ∀ i, (I i).OrdConnected) (hdir : Directed (· ⊆ ·) I)
    {x : ℝ} (hx : x ∈ ⋃ i, I i) :
    ∃ i, x ∈ I i ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ⋃ i, I i, |y - x| < δ → y ∈ I i := by
  obtain ⟨i₀, hx₀⟩ := mem_iUnion.mp hx
  have hleft : ∃ i, x ∈ I i ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ⋃ i, I i, y ≤ x → x - y < δ → y ∈ I i := by
    by_cases h : ∃ a ∈ ⋃ i, I i, a < x
    · obtain ⟨a, ha, hax⟩ := h
      obtain ⟨ia, ha⟩ := mem_iUnion.mp ha
      obtain ⟨i, hi₀, hia⟩ := hdir i₀ ia
      refine ⟨i, hi₀ hx₀, x - a, sub_pos.mpr hax, ?_⟩
      intro y _ hy hδ
      exact (hI i).out (hia ha) (hi₀ hx₀) ⟨by linarith, hy⟩
    · refine ⟨i₀, hx₀, 1, zero_lt_one, ?_⟩
      intro y hy hyx _
      have : x ≤ y := le_of_not_gt (fun hxy => h ⟨y, hy, hxy⟩)
      exact le_antisymm hyx this ▸ hx₀
  have hright : ∃ i, x ∈ I i ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ⋃ i, I i, x ≤ y → y - x < δ → y ∈ I i := by
    by_cases h : ∃ b ∈ ⋃ i, I i, x < b
    · obtain ⟨b, hb, hxb⟩ := h
      obtain ⟨ib, hb⟩ := mem_iUnion.mp hb
      obtain ⟨i, hi₀, hib⟩ := hdir i₀ ib
      refine ⟨i, hi₀ hx₀, b - x, sub_pos.mpr hxb, ?_⟩
      intro y _ hy hδ
      exact (hI i).out (hi₀ hx₀) (hib hb) ⟨hy, by linarith⟩
    · refine ⟨i₀, hx₀, 1, zero_lt_one, ?_⟩
      intro y hy hxy _
      have : y ≤ x := le_of_not_gt (fun hyx => h ⟨y, hy, hyx⟩)
      exact le_antisymm this hxy ▸ hx₀
  obtain ⟨iL, hxL, δL, hδL, hL⟩ := hleft
  obtain ⟨iR, hxR, δR, hδR, hR⟩ := hright
  obtain ⟨i, hiL, hiR⟩ := hdir iL iR
  refine ⟨i, hiL hxL, min δL δR, lt_min hδL hδR, ?_⟩
  intro y hy hδ
  obtain ⟨hδL', hδR'⟩ := lt_min_iff.mp hδ
  rcases le_total y x with hyx | hxy
  · exact hiL (hL y hy hyx (by linarith [neg_le_abs (y - x)]))
  · exact hiR (hR y hy hxy (lt_of_le_of_lt (le_abs_self _) hδR'))

private structure Worldline (F : GeneralizedRicciFlowData.{u}) (origin scale : ℝ) where
  domain : Set ℝ
  connected : domain.OrdConnected
  value : ∀ s, s ∈ domain → (F.slice (origin + s / scale)).carrier
  continuous : Continuous (fun s : domain => (⟨origin + s.1 / scale, value s.1 s.2⟩ : F.point))
  vertical : ∀ s, s ∈ domain →
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' hs', |s' - s| < δ → ∃ hb : origin + s' / scale ∈ (F.box b).interval,
        value s' hs' = (F.box b).forward (origin + s' / scale) hb y

private def Worldline.Extends {F : GeneralizedRicciFlowData.{u}} {origin scale : ℝ}
    (a b : Worldline F origin scale) : Prop :=
  ∃ h : a.domain ⊆ b.domain, ∀ s hs, b.value s (h hs) = a.value s hs

private theorem Worldline.Extends.refl {F : GeneralizedRicciFlowData.{u}} {origin scale : ℝ}
    (a : Worldline F origin scale) : a.Extends a := ⟨Subset.rfl, fun _ _ => rfl⟩

private theorem Worldline.Extends.trans {F : GeneralizedRicciFlowData.{u}} {origin scale : ℝ}
    {a b c : Worldline F origin scale} (hab : a.Extends b) (hbc : b.Extends c) :
    a.Extends c := by
  obtain ⟨hab, eab⟩ := hab
  obtain ⟨hbc, ebc⟩ := hbc
  exact ⟨hab.trans hbc, fun s hs => (ebc s (hab hs)).trans (eab s hs)⟩

private def Worldline.ofCylinder {F : GeneralizedRicciFlowData.{u}}
    {p : F.point} {scale : ℝ} {I : Set ℝ}
    (e : GeneralizedFlowCylinder F (F.slice p.1) p.1 scale I {p.2})
    (hI : I.OrdConnected) : Worldline F p.1 scale where
  domain := I
  connected := hI
  value s hs := e.forward s hs p.2
  continuous := e.embedding.continuous.comp
    (continuous_id.prodMk (continuous_const
      (y := (⟨p.2, mem_singleton p.2⟩ : ({p.2} : Set (F.slice p.1).carrier)))))
  vertical s hs := e.vertical_compatibility s hs p.2 (mem_singleton p.2)

private noncomputable def Worldline.toCylinder {F : GeneralizedRicciFlowData.{u}}
    {p : F.point} {scale : ℝ} (w : Worldline F p.1 scale) (hscale : 0 < scale) :
    GeneralizedFlowCylinder F (F.slice p.1) p.1 scale w.domain {p.2} where
  scale_pos := hscale
  forward s hs _ := w.value s hs
  inverse _ _ _ := p.2
  forward_smooth _ _ := contMDiffOn_const
  inverse_smooth _ _ := contMDiffOn_const
  left_inverse _ _ x hx := mem_singleton_iff.mp hx |>.symm
  right_inverse _ _ _ hx := by obtain ⟨x, _, rfl⟩ := hx; rfl
  embedding := by
    let f : w.domain → F.point := fun s => ⟨p.1 + s.1 / scale, w.value s.1 s.2⟩
    have hf : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp w.continuous
        (show Continuous (fun q : F.point => scale * (q.1 - p.1)) from
          continuous_const.mul (F.time_continuous.sub continuous_const))
      convert (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : w.domain → ℝ)) using 1
      ext s
      simp only [Function.comp_apply]
      field_simp [ne_of_gt hscale]
      ring
    let : Unique ({p.2} : Set (F.slice p.1).carrier) :=
      ⟨⟨p.2, mem_singleton p.2⟩, fun x => Subtype.ext (mem_singleton_iff.mp x.2)⟩
    exact hf.comp (Homeomorph.prodUnique w.domain ({p.2} : Set (F.slice p.1).carrier)).isEmbedding
  vertical_compatibility s hs _ _ := w.vertical s hs

private theorem Worldline.exists_union {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} (a b : Worldline F origin scale)
    {s₀ : ℝ} (ha : s₀ ∈ interior a.domain) (hb : s₀ ∈ interior b.domain)
    (hcompat : ∀ s (hs : s ∈ a.domain) (hs' : s ∈ b.domain), a.value s hs = b.value s hs') :
    ∃ w : Worldline F origin scale,
      w.domain = a.domain ∪ b.domain ∧ a.Extends w ∧ b.Extends w := by
  classical
  let D := a.domain ∪ b.domain
  let v (s : ℝ) (hs : s ∈ D) :=
    if h : s ∈ a.domain then a.value s h else b.value s (hs.resolve_left h)
  have hv (w : Worldline F origin scale) (hw : w = a ∨ w = b)
      (s : ℝ) (hs : s ∈ D) (hsw : s ∈ w.domain) : v s hs = w.value s hsw := by
    rcases hw with rfl | rfl
    · simp only [v, dif_pos hsw]
    · by_cases hsa : s ∈ a.domain
      · simpa only [v, dif_pos hsa] using hcompat s hsa hsw
      · simp only [v, dif_neg hsa]
  have hlocal (s : ℝ) (hs : s ∈ D) :
      ∃ w : Worldline F origin scale, (w = a ∨ w = b) ∧ s ∈ w.domain ∧
        ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ D, |t - s| < delta → t ∈ w.domain := by
    obtain ⟨K, hK, hsK, delta, hd, hnear⟩ :=
      overlapping_intervals_local a.connected b.connected ha hb hs
    rcases hK with rfl | rfl
    · exact ⟨a, Or.inl rfl, hsK, delta, hd, hnear⟩
    · exact ⟨b, Or.inr rfl, hsK, delta, hd, hnear⟩
  have hcont : Continuous (fun s : D => (⟨origin + s.1 / scale, v s.1 s.2⟩ : F.point)) := by
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨w, hw, _, delta, hd, hnear⟩ := hlocal s.1 s.2
    let V : Set D := {t | |t.1 - s.1| < delta}
    have hV : IsOpen V := isOpen_lt
      ((continuous_subtype_val.sub continuous_const).abs) continuous_const
    have hsV : s ∈ V := by simpa [V] using hd
    have hmap (t : V) : t.1.1 ∈ w.domain := hnear _ t.1.2 t.2
    have hmap_cont : Continuous (fun t : V => (⟨t.1.1, hmap t⟩ : w.domain)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have heq : (fun t : V => (⟨origin + t.1.1 / scale, v t.1.1 t.1.2⟩ : F.point)) =
        (fun t : w.domain => (⟨origin + t.1 / scale, w.value t.1 t.2⟩ : F.point)) ∘
          (fun t : V => (⟨t.1.1, hmap t⟩ : w.domain)) := by
      funext t
      exact congrArg (Sigma.mk (origin + t.1.1 / scale)) (hv w hw _ t.1.2 (hmap t))
    have hCV : ContinuousOn
        (fun s : D => (⟨origin + s.1 / scale, v s.1 s.2⟩ : F.point)) V := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      change Continuous (fun t : V => (⟨origin + t.1.1 / scale, v t.1.1 t.1.2⟩ : F.point))
      rw [heq]
      exact w.continuous.comp hmap_cont
    exact hCV.continuousAt (hV.mem_nhds hsV)
  have hvert : ∀ s, s ∈ D →
      ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ delta : ℝ, 0 < delta ∧
        ∀ s' hs', |s' - s| < delta → ∃ hb : origin + s' / scale ∈ (F.box b).interval,
          v s' hs' = (F.box b).forward (origin + s' / scale) hb y := by
    intro s hs
    obtain ⟨w, hw, hsw, delta, hd, hnear⟩ := hlocal s hs
    obtain ⟨box, y, eta, heta, hbox⟩ := w.vertical s hsw
    refine ⟨box, y, min delta eta, lt_min hd heta, ?_⟩
    intro s' hs' hclose
    obtain ⟨ht, hval⟩ := hbox s' (hnear s' hs' (lt_min_iff.mp hclose).1)
      (lt_min_iff.mp hclose).2
    exact ⟨ht, (hv w hw s' hs' _).trans hval⟩
  let w : Worldline F origin scale := {
    domain := D
    connected := (IsPreconnected.union s₀ (interior_subset ha) (interior_subset hb)
      a.connected.isPreconnected b.connected.isPreconnected).ordConnected
    value := v
    continuous := hcont
    vertical := hvert }
  refine ⟨w, rfl, ⟨subset_union_left, ?_⟩, ⟨subset_union_right, ?_⟩⟩
  · intro s hs
    exact hv a (Or.inl rfl) s (Or.inl hs) hs
  · intro s hs
    exact hv b (Or.inr rfl) s (Or.inr hs) hs

private theorem Worldline.chain_upper_bound {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} (c : Set (Worldline F origin scale))
    (hc : IsChain Worldline.Extends c) :
    ∃ w : Worldline F origin scale, ∀ a ∈ c, a.Extends w := by
  classical
  let : Std.Refl (@Worldline.Extends F origin scale) :=
    ⟨Worldline.Extends.refl⟩
  let I : c → Set ℝ := fun i => i.1.domain
  let D : Set ℝ := ⋃ i, I i
  have hdir : Directed (· ⊆ ·) I := by
    intro i j
    rcases hc.total i.2 j.2 with hij | hji
    · exact ⟨j, hij.1, Subset.rfl⟩
    · exact ⟨i, Subset.rfl, hji.1⟩
  have hconn : D.OrdConnected := by
    constructor
    intro x hx y hy z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact mem_iUnion.mpr ⟨k, k.1.connected.out (hik hi) (hjk hj) hz⟩
  let idx (s : ℝ) (hs : s ∈ D) : c := Classical.choose (mem_iUnion.mp hs)
  have hidx (s : ℝ) (hs : s ∈ D) : s ∈ I (idx s hs) :=
    Classical.choose_spec (mem_iUnion.mp hs)
  let v (s : ℝ) (hs : s ∈ D) := (idx s hs).1.value s (hidx s hs)
  have hv (i : c) (s : ℝ) (hs : s ∈ D) (hi : s ∈ I i) :
      v s hs = i.1.value s hi := by
    rcases hc.total (idx s hs).2 i.2 with h | h
    · exact (h.2 s (hidx s hs)).symm
    · exact h.2 s hi
  have hlocal (s : ℝ) (hs : s ∈ D) : ∃ i : c, s ∈ I i ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ D, |y - s| < δ → y ∈ I i :=
    directed_intervals_local I (fun i => i.1.connected) hdir hs
  have hcont : Continuous (fun s : D => (⟨origin + s.1 / scale, v s.1 s.2⟩ : F.point)) := by
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨i, _, δ, hδ, hi⟩ := hlocal s.1 s.2
    let V : Set D := {r | |r.1 - s.1| < δ}
    have hV : IsOpen V := isOpen_lt
      ((continuous_subtype_val.sub continuous_const).abs) continuous_const
    have hsV : s ∈ V := by simpa [V] using hδ
    have hVI (r : V) : r.1.1 ∈ I i := hi _ r.1.2 r.2
    have hmap : Continuous (fun r : V => (⟨r.1.1, hVI r⟩ : I i)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have heq : (fun r : V => (⟨origin + r.1.1 / scale, v r.1.1 r.1.2⟩ : F.point)) =
        (fun s : i.1.domain => (⟨origin + s.1 / scale, i.1.value s.1 s.2⟩ : F.point)) ∘
          (fun r : V => (⟨r.1.1, hVI r⟩ : I i)) := by
      funext r
      exact congrArg (Sigma.mk (origin + r.1.1 / scale)) (hv i _ r.1.2 (hVI r))
    have hCV : ContinuousOn
        (fun s : D => (⟨origin + s.1 / scale, v s.1 s.2⟩ : F.point)) V := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      change Continuous (fun r : V => (⟨origin + r.1.1 / scale, v r.1.1 r.1.2⟩ : F.point))
      rw [heq]
      exact i.1.continuous.comp hmap
    exact hCV.continuousAt (hV.mem_nhds hsV)
  have hvert : ∀ s, s ∈ D →
      ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
        ∀ s' hs', |s' - s| < δ → ∃ hb : origin + s' / scale ∈ (F.box b).interval,
          v s' hs' = (F.box b).forward (origin + s' / scale) hb y := by
    intro s hs
    obtain ⟨i, hsi, δ, hδ, hi⟩ := hlocal s hs
    obtain ⟨b, y, ε, hε, hb⟩ := i.1.vertical s hsi
    refine ⟨b, y, min δ ε, lt_min hδ hε, ?_⟩
    intro s' hs' hclose
    obtain ⟨hcloseδ, hcloseε⟩ := lt_min_iff.mp hclose
    obtain ⟨ht, hvb⟩ := hb s' (hi s' hs' hcloseδ) hcloseε
    exact ⟨ht, (hv i s' hs' _).trans hvb⟩
  let w : Worldline F origin scale := ⟨D, hconn, v, hcont, hvert⟩
  refine ⟨w, ?_⟩
  intro a ha
  refine ⟨fun _ hs => mem_iUnion.mpr ⟨⟨a, ha⟩, hs⟩, ?_⟩
  intro s hs
  exact hv ⟨a, ha⟩ s (mem_iUnion.mpr ⟨⟨a, ha⟩, hs⟩) hs

private theorem Worldline.exists_maximal {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} (seed : Worldline F origin scale) :
    ∃ w : Worldline F origin scale, seed.Extends w ∧
      ∀ w', w.Extends w' → w'.Extends w := by
  let C := {w : Worldline F origin scale // seed.Extends w}
  let r : C → C → Prop := fun a b => a.1.Extends b.1
  let : Nonempty C := ⟨⟨seed, Worldline.Extends.refl seed⟩⟩
  have hbound : ∀ c : Set C, IsChain r c → c.Nonempty →
      ∃ b : C, ∀ a ∈ c, r a b := by
    intro c hc hne
    have hchain : IsChain Worldline.Extends (Subtype.val '' c) := by
      rintro a ⟨a', ha, rfl⟩ b ⟨b', hb, rfl⟩ hab
      exact hc ha hb (fun h => hab (congrArg Subtype.val h))
    obtain ⟨w, hw⟩ := Worldline.chain_upper_bound (Subtype.val '' c) hchain
    obtain ⟨a, ha⟩ := hne
    refine ⟨⟨w, a.2.trans (hw a.1 ⟨a, ha, rfl⟩)⟩, ?_⟩
    intro b hb
    exact hw b.1 ⟨b, hb, rfl⟩
  obtain ⟨w, hw⟩ := exists_maximal_of_nonempty_chains_bounded hbound
    (fun {_ _ _} h₁ h₂ => Worldline.Extends.trans h₁ h₂)
  refine ⟨w.1, w.2, ?_⟩
  intro w' hww'
  exact hw ⟨w', w.2.trans hww'⟩ hww'

private def castSlice {F : GeneralizedRicciFlowData.{u}} (p : F.point)
    {t : ℝ} (h : p.1 = t) : (F.slice t).carrier := h ▸ p.2

private theorem castSlice_point {F : GeneralizedRicciFlowData.{u}} (p : F.point)
    {t : ℝ} (h : p.1 = t) : (⟨t, castSlice p h⟩ : F.point) = p := by
  cases p
  cases h
  rfl

private noncomputable def Worldline.ofCurve {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} (I : Set ℝ) (hI : I.OrdConnected)
    (γ : I → F.point) (htime : ∀ s, (γ s).1 = origin + s.1 / scale)
    (hcont : Continuous γ)
    (hvert : ∀ s : I, ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' : I, |s'.1 - s.1| < δ → ∃ hb : origin + s'.1 / scale ∈ (F.box b).interval,
        γ s' = ⟨origin + s'.1 / scale, (F.box b).forward (origin + s'.1 / scale) hb y⟩) :
    Worldline F origin scale where
  domain := I
  connected := hI
  value s hs := castSlice (γ ⟨s, hs⟩) (htime ⟨s, hs⟩)
  continuous := by
    convert hcont using 1
    funext s
    exact castSlice_point (γ s) (htime s)
  vertical s hs := by
    obtain ⟨b, y, δ, hδ, hb⟩ := hvert ⟨s, hs⟩
    refine ⟨b, y, δ, hδ, ?_⟩
    intro s' hs' hclose
    obtain ⟨ht, hγ⟩ := hb ⟨s', hs'⟩ hclose
    exact ⟨ht, eq_of_heq (Sigma.mk.inj
      ((castSlice_point (γ ⟨s', hs'⟩) (htime ⟨s', hs'⟩)).trans hγ)).2⟩

private noncomputable def Worldline.rescale {F : GeneralizedRicciFlowData.{u}}
    {origin r q : ℝ} (w : Worldline F origin r) (hr : 0 < r) (hq : 0 < q) :
    Worldline F origin q := by
  let I := (fun s : ℝ => s * r / q) ⁻¹' w.domain
  have hI : I.OrdConnected := w.connected.preimage_mono
    (fun _ _ h => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hr.le) hq.le)
  let f (s : I) : w.domain := ⟨s.1 * r / q, s.2⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.mul continuous_const).div_const q).subtype_mk _
  let γ (s : I) : F.point := ⟨origin + (f s).1 / r, w.value (f s).1 (f s).2⟩
  have hclock (s : ℝ) : origin + (s * r / q) / r = origin + s / q := by
    field_simp
  have htime (s : I) : (γ s).1 = origin + s.1 / q := hclock s.1
  apply Worldline.ofCurve I hI γ htime (w.continuous.comp hf)
  intro s
  obtain ⟨b, y, δ, hδ, hb⟩ := w.vertical (f s).1 (f s).2
  refine ⟨b, y, δ * q / r, div_pos (mul_pos hδ hq) hr, ?_⟩
  intro s' hclose
  have hclose' : |(f s').1 - (f s).1| < δ := by
    change |s'.1 * r / q - s.1 * r / q| < δ
    rw [show s'.1 * r / q - s.1 * r / q = (s'.1 - s.1) * r / q by ring,
      abs_div, abs_mul, abs_of_pos hr, abs_of_pos hq]
    apply (div_lt_iff₀ hq).mpr
    exact (lt_div_iff₀ hr).mp hclose
  obtain ⟨ht, hv⟩ := hb (f s').1 (f s').2 hclose'
  refine ⟨hclock s'.1 ▸ ht, ?_⟩
  change (⟨origin + (s'.1 * r / q) / r, w.value _ _⟩ : F.point) = _
  rw [hv]
  have hbox (a a' : ℝ) (ha : a ∈ (F.box b).interval)
      (ha' : a' ∈ (F.box b).interval) (haa' : a = a') :
      (⟨a, (F.box b).forward a ha y⟩ : F.point) =
        ⟨a', (F.box b).forward a' ha' y⟩ := by
    subst a'
    rfl
  exact hbox _ _ _ _ (hclock s'.1)

private noncomputable def Worldline.shift {F : GeneralizedRicciFlowData.{u}}
    {origin origin' scale a : ℝ} (w : Worldline F origin scale)
    (horigin : origin = origin' + a / scale) : Worldline F origin' scale := by
  let I := (fun s : ℝ => s - a) ⁻¹' w.domain
  have hI : I.OrdConnected := w.connected.preimage_mono
    (fun _ _ h => sub_le_sub_right h a)
  let f (s : I) : w.domain := ⟨s.1 - a, s.2⟩
  have hf : Continuous f :=
    (continuous_subtype_val.sub continuous_const).subtype_mk _
  let γ (s : I) : F.point := ⟨origin + (f s).1 / scale, w.value (f s).1 (f s).2⟩
  have hclock (s : ℝ) : origin + (s - a) / scale = origin' + s / scale := by
    rw [horigin]
    ring
  apply Worldline.ofCurve I hI γ (fun s => hclock s.1) (w.continuous.comp hf)
  intro s
  obtain ⟨b, y, δ, hδ, hb⟩ := w.vertical (f s).1 (f s).2
  refine ⟨b, y, δ, hδ, ?_⟩
  intro s' hclose
  have hclose' : |(f s').1 - (f s).1| < δ := by
    simpa only [f, sub_sub_sub_cancel_right] using hclose
  obtain ⟨ht, hv⟩ := hb (f s').1 (f s').2 hclose'
  refine ⟨hclock s'.1 ▸ ht, ?_⟩
  change (⟨origin + (s'.1 - a) / scale, w.value _ _⟩ : F.point) = _
  rw [hv]
  have hbox (t t' : ℝ) (ht : t ∈ (F.box b).interval)
      (ht' : t' ∈ (F.box b).interval) (htt' : t = t') :
      (⟨t, (F.box b).forward t ht y⟩ : F.point) =
        ⟨t', (F.box b).forward t' ht' y⟩ := by
    subst t'
    rfl
  exact hbox _ _ _ _ (hclock s'.1)

theorem exists_rebased_singleton_cylinder
    {F : GeneralizedRicciFlowData.{u}} {p p' : F.point} {r q a : ℝ} {I : Set ℝ}
    (e : GeneralizedFlowCylinder F (F.slice p'.1) p'.1 r I {p'.2})
    (hI : I.OrdConnected) (hq : 0 < q) (horigin : p'.1 = p.1 + a / q) :
    ∃ e' : GeneralizedFlowCylinder F (F.slice p.1) p.1 q
        ((fun t : ℝ => (t - a) * r / q) ⁻¹' I) {p.2},
      ∀ t ht, e'.pointMap t ht p.2 = e.pointMap ((t - a) * r / q) ht p'.2 := by
  let w := ((Worldline.ofCylinder e hI).rescale e.scale_pos hq).shift horigin
  let e' := w.toCylinder hq
  refine ⟨e', ?_⟩
  intro t ht
  exact (castSlice_point _ _).trans (castSlice_point _ _)

theorem exists_maximalBackwardFlowLine_of_cylinder
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {scale duration : ℝ} {I : Set ℝ}
    (e : GeneralizedFlowCylinder F (F.slice p.1) p.1 scale I {p.2})
    (hI : I.OrdConnected) (hzero : 0 ∈ I)
    (hidentity : e.pointMap 0 hzero p.2 = p)
    (hrequested : Icc (-duration) 0 ⊆ I) :
    ∃ L : GeneralizedMaximalBackwardFlowLine F p scale duration,
      ∃ h : I ⊆ L.maximal_interval,
        ∀ s hs, L.embedding.pointMap s (h hs) p.2 = e.pointMap s hs p.2 := by
  let seed := Worldline.ofCylinder e hI
  obtain ⟨w, hseed, hw⟩ := Worldline.exists_maximal seed
  let E := w.toCylinder e.scale_pos
  have hval (s : ℝ) (hs : s ∈ I) : E.pointMap s (hseed.1 hs) p.2 = e.pointMap s hs p.2 :=
    congrArg (Sigma.mk (p.1 + s / scale)) (hseed.2 s hs)
  let L : GeneralizedMaximalBackwardFlowLine F p scale duration := {
    maximal_interval := w.domain
    maximal_interval_mem_zero := hseed.1 hzero
    maximal_interval_ordConnected := w.connected
    embedding := E
    zero_identity := (hval 0 hzero).trans hidentity
    requested_interval_subset := hrequested.trans hseed.1
    maximal := by
      intro I' e' hI' hsub heq
      have hext : w.Extends (Worldline.ofCylinder e' hI') := by
        refine ⟨hsub, ?_⟩
        intro s hs
        exact eq_of_heq (Sigma.mk.inj (heq s hs)).2
      exact Subset.antisymm (hw _ hext).1 hsub }
  exact ⟨L, hseed.1, hval⟩

theorem maximalBackwardFlowLine_of_rescaled_cylinder
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {r q duration : ℝ} {I : Set ℝ}
    (e : GeneralizedFlowCylinder F (F.slice p.1) p.1 r I {p.2})
    (hI : I.OrdConnected) (hzero : 0 ∈ I)
    (hidentity : e.pointMap 0 hzero p.2 = p) (hq : 0 < q)
    (hrequested : ∀ s ∈ Icc (-duration) 0, s * r / q ∈ I) :
    Nonempty (GeneralizedMaximalBackwardFlowLine F p q duration) := by
  let w := (Worldline.ofCylinder e hI).rescale e.scale_pos hq
  have hz : 0 ∈ w.domain := by
    simpa [w, Worldline.rescale, Worldline.ofCurve, Worldline.ofCylinder] using hzero
  let e' := w.toCylinder hq
  have hid : e'.pointMap 0 hz p.2 = p := by
    have hpack : e'.pointMap 0 hz p.2 = e.pointMap (0 * r / q) hz p.2 :=
      castSlice_point _ _
    exact hpack.trans (by simpa only [zero_mul, zero_div] using hidentity)
  obtain ⟨L, _⟩ := exists_maximalBackwardFlowLine_of_cylinder e' w.connected hz hid hrequested
  exact ⟨L⟩

theorem maximalBackwardFlowLine_contains_overlapping_cylinder
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {scale duration : ℝ}
    (L : GeneralizedMaximalBackwardFlowLine F p scale duration)
    {I : Set ℝ} (e : GeneralizedFlowCylinder F (F.slice p.1) p.1 scale I {p.2})
    (hI : I.OrdConnected)
    (hinter : (interior L.maximal_interval ∩ interior I).Nonempty)
    {s : ℝ} (hs : s ∈ L.maximal_interval) (hs' : s ∈ I)
    (hmeet : L.embedding.pointMap s hs p.2 = e.pointMap s hs' p.2) :
    I ⊆ L.maximal_interval := by
  let a := Worldline.ofCylinder L.embedding L.maximal_interval_ordConnected
  let b := Worldline.ofCylinder e hI
  obtain ⟨s₀, ha, hb⟩ := hinter
  have hcompat : ∀ t (ht : t ∈ a.domain) (ht' : t ∈ b.domain), a.value t ht = b.value t ht' := by
    intro t ht ht'
    have h := L.embedding.pointMap_eq_on_overlap e L.maximal_interval_ordConnected hI
      (mem_singleton p.2) (mem_singleton p.2) hs hs' hmeet t ht ht'
    exact eq_of_heq (Sigma.mk.inj h).2
  obtain ⟨w, _, hwa, hwb⟩ := Worldline.exists_union a b ha hb hcompat
  let E := w.toCylinder e.scale_pos
  have hdom : w.domain = L.maximal_interval :=
    L.maximal w.domain E w.connected hwa.1 (fun t ht =>
      congrArg (Sigma.mk (p.1 + t / scale)) (hwa.2 t ht))
  exact hwb.1.trans (subset_of_eq hdom)

end PoincareConjecture.DeepHorn
