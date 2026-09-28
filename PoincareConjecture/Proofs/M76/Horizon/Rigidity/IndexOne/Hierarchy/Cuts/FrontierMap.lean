import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}

noncomputable def markedCutFrontierMap (P : OriginalDiskProduct e N j)
    (q : W → X) (l u : ℝ) (z : W) : X := by
  classical
  exact if z.2 = l then P.map (z.1, (1 / 2 : ℝ)) else
    if z.2 = u then P.map (z.1, -(1 / 2 : ℝ)) else q z

theorem markedCutFrontierMap_lower (P : OriginalDiskProduct e N j)
    (q : W → X) (l u : ℝ) (z : V2) :
    P.markedCutFrontierMap q l u (z, l) = P.map (z, (1 / 2 : ℝ)) := by
  simp [markedCutFrontierMap]

theorem markedCutFrontierMap_upper (P : OriginalDiskProduct e N j)
    (q : W → X) {l u : ℝ} (hlu : l < u) (z : V2) :
    P.markedCutFrontierMap q l u (z, u) = P.map (z, -(1 / 2 : ℝ)) := by
  simp [markedCutFrontierMap, ne_of_gt hlu]

theorem markedCutFrontierMap_lateral (P : OriginalDiskProduct e N j)
    (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (z : W) (hz : z.1 ∈ Q) : P.markedCutFrontierMap q l u z = q z := by
  classical
  by_cases hl : z.2 = l
  · have heq : z = (z.1, l) := Prod.ext rfl hl
    rw [heq, P.markedCutFrontierMap_lower]
    exact (hlower _ hz).symm
  · by_cases hu : z.2 = u
    · have heq : z = (z.1, u) := Prod.ext rfl hu
      rw [heq, P.markedCutFrontierMap_upper q hlu]
      exact (hupper _ hz).symm
    · simp [markedCutFrontierMap, hl, hu]

theorem markedCutFrontierMap_frontier_iff (P : OriginalDiskProduct e N j)
    (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (hqN : MapsTo q (Q ×ˢ Icc l u) (frontier N))
    (z : W) (hz : z ∈ cubePrismBoundary l u) :
    P.markedCutFrontierMap q l u z ∈ frontier N ↔ z.1 ∈ Q := by
  rcases hz with hlat | hcap
  · rw [P.markedCutFrontierMap_lateral q hlu hlower hupper z hlat.1]
    exact iff_of_true (hqN hlat) hlat.1
  · rcases hcap.2 with hl | hu
    · have heq : z = (z.1, l) := Prod.ext rfl hl
      rw [heq, P.markedCutFrontierMap_lower]
      exact P.proper (z.1, (1 / 2 : ℝ)) ⟨hcap.1, by norm_num⟩
    · have heq : z = (z.1, u) := Prod.ext rfl hu
      rw [heq, P.markedCutFrontierMap_upper q hlu]
      exact P.proper (z.1, -(1 / 2 : ℝ)) ⟨hcap.1, by norm_num⟩

private theorem markedCutFrontierMap_injOn_caps (P : OriginalDiskProduct e N j)
    (q : W → X) {l u : ℝ} (hlu : l < u) :
    InjOn (P.markedCutFrontierMap q l u) (D ×ˢ ({l, u} : Set ℝ)) := by
  intro z hz w hw heq
  have hzplus : (z.1, (1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hz.1, by norm_num⟩
  have hzminus : (z.1, -(1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hz.1, by norm_num⟩
  have hwplus : (w.1, (1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hw.1, by norm_num⟩
  have hwminus : (w.1, -(1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hw.1, by norm_num⟩
  rcases hz.2 with hz' | hz' <;> rcases hw.2 with hw' | hw'
  · have hzz : z = (z.1, l) := Prod.ext rfl hz'
    have hww : w = (w.1, l) := Prod.ext rfl hw'
    rw [hzz, hww, P.markedCutFrontierMap_lower, P.markedCutFrontierMap_lower] at heq
    have hfirst := congrArg Prod.fst (P.injective hzplus hwplus heq)
    exact Prod.ext hfirst (hz'.trans hw'.symm)
  · have hzz : z = (z.1, l) := Prod.ext rfl hz'
    have hww : w = (w.1, u) := Prod.ext rfl hw'
    rw [hzz, hww, P.markedCutFrontierMap_lower, P.markedCutFrontierMap_upper q hlu] at heq
    have hh := congrArg Prod.snd (P.injective hzplus hwminus heq)
    norm_num at hh
  · have hzz : z = (z.1, u) := Prod.ext rfl hz'
    have hww : w = (w.1, l) := Prod.ext rfl hw'
    rw [hzz, hww, P.markedCutFrontierMap_upper q hlu, P.markedCutFrontierMap_lower] at heq
    have hh := congrArg Prod.snd (P.injective hzminus hwplus heq)
    norm_num at hh
  · have hzz : z = (z.1, u) := Prod.ext rfl hz'
    have hww : w = (w.1, u) := Prod.ext rfl hw'
    rw [hzz, hww, P.markedCutFrontierMap_upper q hlu,
      P.markedCutFrontierMap_upper q hlu] at heq
    have hfirst := congrArg Prod.fst (P.injective hzminus hwminus heq)
    exact Prod.ext hfirst (hz'.trans hw'.symm)

theorem markedCutFrontierMap_injOn (P : OriginalDiskProduct e N j)
    (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (hqN : MapsTo q (Q ×ˢ Icc l u) (frontier N))
    (hqi : InjOn q (Q ×ˢ Icc l u)) :
    InjOn (P.markedCutFrontierMap q l u) (cubePrismBoundary l u) := by
  have htime (z : W) (hz : z ∈ cubePrismBoundary l u) : z.2 ∈ Icc l u := by
    rcases hz with hlat | hcap
    · exact hlat.2
    · rcases hcap.2 with hl | hu <;> rw [show z.2 = _ from ‹_›] <;>
        exact ⟨by linarith, by linarith⟩
  intro z hz w hw heq
  by_cases hzQ : z.1 ∈ Q
  · have hwQ : w.1 ∈ Q := (P.markedCutFrontierMap_frontier_iff q hlu
      hlower hupper hqN w hw).mp (heq ▸
        (P.markedCutFrontierMap_frontier_iff q hlu hlower hupper hqN z hz).mpr hzQ)
    rw [P.markedCutFrontierMap_lateral q hlu hlower hupper z hzQ,
      P.markedCutFrontierMap_lateral q hlu hlower hupper w hwQ] at heq
    exact hqi ⟨hzQ, htime z hz⟩ ⟨hwQ, htime w hw⟩ heq
  · have hwQ : w.1 ∉ Q := by
      intro hwQ
      apply hzQ
      exact (P.markedCutFrontierMap_frontier_iff q hlu hlower hupper hqN z hz).mp
        (heq.symm ▸ (P.markedCutFrontierMap_frontier_iff q hlu hlower hupper hqN w hw).mpr hwQ)
    exact P.markedCutFrontierMap_injOn_caps q hlu
      (hz.elim (fun h => (hzQ h.1).elim) id)
      (hw.elim (fun h => (hwQ h.1).elim) id) heq

theorem markedCutFrontierMap_image (P : OriginalDiskProduct e N j)
    (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ))) :
    P.markedCutFrontierMap q l u '' cubePrismBoundary l u =
      (q '' (Q ×ˢ Icc l u)) ∪ P.endDisks := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hlat | hcap
    · exact Or.inl ⟨z, hlat, (P.markedCutFrontierMap_lateral q hlu hlower hupper z hlat.1).symm⟩
    · apply Or.inr
      rcases hcap.2 with hl | hu
      · refine ⟨(z.1, (1 / 2 : ℝ)), ⟨hcap.1, by simp⟩, ?_⟩
        rw [show z = (z.1, l) from Prod.ext rfl hl, P.markedCutFrontierMap_lower]
      · refine ⟨(z.1, -(1 / 2 : ℝ)), ⟨hcap.1, by simp⟩, ?_⟩
        rw [show z = (z.1, u) from Prod.ext rfl hu, P.markedCutFrontierMap_upper q hlu]
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, Or.inl hz, P.markedCutFrontierMap_lateral q hlu hlower hupper z hz.1⟩
    · rcases hz.2 with hm | hp
      · refine ⟨(z.1, u), Or.inr ⟨hz.1, by simp⟩, ?_⟩
        rw [P.markedCutFrontierMap_upper q hlu]
        exact congrArg P.map (Prod.ext rfl hm.symm)
      · refine ⟨(z.1, l), Or.inr ⟨hz.1, by simp⟩, ?_⟩
        rw [P.markedCutFrontierMap_lower]
        exact congrArg P.map (Prod.ext rfl hp.symm)

end PoincareConjecture.M76.OriginalDiskProduct
