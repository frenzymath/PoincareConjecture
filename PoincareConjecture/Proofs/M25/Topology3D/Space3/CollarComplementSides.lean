import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarOrientation

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [Nonempty X] [PreconnectedSpace X]

theorem collar_complement_halves (Q : OpenPartialHomeomorph (X × ℝ) Y)
    {d : ℝ} (hd : 0 < d) (hs : Q.source = univ ×ˢ Ioo (-d) d)
    {A B Γ : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = Γᶜ) (hcentral : Q '' (univ ×ˢ {0}) = Γ)
    (hclosure : Γ ⊆ closure A ∩ closure B) :
    (Q '' (univ ×ˢ Ioo (-d) 0) ⊆ A ∧ Q '' (univ ×ˢ Ioo 0 d) ⊆ B) ∨
      (Q '' (univ ×ˢ Ioo (-d) 0) ⊆ B ∧ Q '' (univ ×ˢ Ioo 0 d) ⊆ A) := by
  classical
  let N := Q '' (univ ×ˢ Ioo (-d) 0)
  let P := Q '' (univ ×ˢ Ioo 0 d)
  have h0 (x : X) : (x, (0 : ℝ)) ∈ Q.source := by
    rw [hs]
    exact ⟨mem_univ _, neg_neg_of_pos hd, hd⟩
  have hNsrc : (univ : Set X) ×ˢ Ioo (-d) 0 ⊆ Q.source := by
    rw [hs]
    exact fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hd⟩
  have hPsrc : (univ : Set X) ×ˢ Ioo 0 d ⊆ Q.source := by
    rw [hs]
    exact fun p hp => ⟨hp.1, (neg_neg_of_pos hd).trans hp.2.1, hp.2.2⟩
  have hN : IsPreconnected N :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image Q (Q.continuousOn.mono hNsrc)
  have hP : IsPreconnected P :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image Q (Q.continuousOn.mono hPsrc)
  have hnot (p : X × ℝ) (hp : p ∈ Q.source) (hp0 : p.2 ≠ 0) : Q p ∉ Γ := by
    rw [← hcentral]
    rintro ⟨q, hq, heq⟩
    have hq0 : q.2 = 0 := hq.2
    have hqsrc : q ∈ Q.source := by
      simpa only [← hq0, Prod.eta] using h0 q.1
    exact hp0 ((congrArg Prod.snd (Q.injOn hp hqsrc heq.symm)).trans hq0)
  have hNcover : N ⊆ A ∪ B := by
    rw [hcover]
    rintro y ⟨p, hp, rfl⟩
    exact hnot p (hNsrc hp) hp.2.2.ne
  have hPcover : P ⊆ A ∪ B := by
    rw [hcover]
    rintro y ⟨p, hp, rfl⟩
    exact hnot p (hPsrc hp) hp.2.1.ne'
  have hhalf (y : Y) (hy : y ∈ Q.target) (hyΓ : y ∉ Γ) : y ∈ N ∪ P := by
    let p := Q.symm y
    have hp : p ∈ (univ : Set X) ×ˢ Ioo (-d) d := hs ▸ Q.map_target hy
    have hp0 : p.2 ≠ 0 := by
      intro hz
      apply hyΓ
      rw [← hcentral]
      exact ⟨p, ⟨mem_univ _, hz⟩, Q.right_inv hy⟩
    rcases lt_or_gt_of_ne hp0 with hn | hp'
    · exact Or.inl ⟨p, ⟨hp.1, hp.2.1, hn⟩, Q.right_inv hy⟩
    · exact Or.inr ⟨p, ⟨hp.1, hp', hp.2.2⟩, Q.right_inv hy⟩
  let x : X := Classical.choice inferInstance
  have hxΓ : Q (x, 0) ∈ Γ := by
    rw [← hcentral]
    exact ⟨(x, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hxt : Q (x, 0) ∈ Q.target := Q.map_source (h0 x)
  have hside := hclosure hxΓ
  obtain ⟨a, hat, ha⟩ := mem_closure_iff.mp hside.1 Q.target Q.open_target hxt
  obtain ⟨b, hbt, hb⟩ := mem_closure_iff.mp hside.2 Q.target Q.open_target hxt
  have haΓ : a ∉ Γ := by
    have h : a ∈ A ∪ B := Or.inl ha
    rwa [hcover] at h
  have hbΓ : b ∉ Γ := by
    have h : b ∈ A ∪ B := Or.inr hb
    rwa [hcover] at h
  have hahalf := hhalf a hat haΓ
  have hbhalf := hhalf b hbt hbΓ
  change (N ⊆ A ∧ P ⊆ B) ∨ (N ⊆ B ∧ P ⊆ A)
  rcases hN.subset_or_subset hA hB hAB hNcover with hNA | hNB <;>
    rcases hP.subset_or_subset hA hB hAB hPcover with hPA | hPB
  · exact (Set.disjoint_left.mp hAB (hbhalf.elim (fun h => hNA h) (fun h => hPA h)) hb).elim
  · exact Or.inl ⟨hNA, hPB⟩
  · exact Or.inr ⟨hNB, hPA⟩
  · exact (Set.disjoint_left.mp hAB ha (hahalf.elim (fun h => hNB h) (fun h => hPB h))).elim

end PoincareConjecture.M25.Topology3D
