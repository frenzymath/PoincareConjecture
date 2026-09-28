import PoincareConjecture.Proofs.M08.ChartCover
import Mathlib.Order.RelSeries
import Mathlib.Order.Fin.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

namespace PoincareConjecture.M08

theorem exists_compact_partition_at {X ι : Type*}
    [MetricSpace X] [LocallyCompactSpace X] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {A B s : ℝ} (hs : s ∈ Ioo A B) (γ : ℝ → X) (hγ : Continuous γ) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (c : Fin m → ι) (K : Fin m → Set X)
      (j : Fin m), Monotone t ∧ t 0 = A ∧ t (Fin.last m) = B ∧
      (∀ i, IsCompact (K i) ∧
        γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (K i) ∧ K i ⊆ U (c i)) ∧
      A < t j.castSucc ∧ t j.castSucc < s ∧ s < t j.succ ∧ t j.succ < B := by
  classical
  let R : Set (ℝ × ℝ) := {z | z.1 ≤ z.2 ∧ ∃ i K, IsCompact K ∧
    γ '' Icc z.1 z.2 ⊆ interior K ∧ K ⊆ U i}
  have partition (a b : ℝ) (hab : a ≤ b) :
      ∃ p : RelSeries R, p.head = a ∧ p.last = b := by
    have hlim : TendstoUniformlyOn (fun _ : ℕ ↦ γ) γ atTop (Icc a b) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      exact Eventually.of_forall (fun _ _ _ ↦ by simpa only [dist_self] using hε)
    obtain ⟨m, t, c, K, _, ht, hta, htb, hK, _⟩ :=
      exists_compact_partition_of_uniform_limit U hU hcover hab γ hγ (fun _ ↦ γ) hlim
    let p : RelSeries R := ⟨m, t, fun i ↦ ⟨ht (Fin.castSucc_le_succ i),
      c i, K i, hK i⟩⟩
    exact ⟨p, hta, htb⟩
  obtain ⟨i, hi⟩ := hcover (γ s)
  obtain ⟨K, hK, hγK, hKU⟩ := exists_compact_between isCompact_singleton (hU i)
    (singleton_subset_iff.mpr hi)
  have hS : Ioo A B ∩ γ ⁻¹' interior K ∈ 𝓝 s :=
    (isOpen_Ioo.inter (isOpen_interior.preimage hγ)).mem_nhds
      ⟨hs, hγK (mem_singleton _)⟩
  obtain ⟨a, b, _, habmem, habS⟩ := exists_Icc_mem_subset_of_mem_nhds hS
  have hsab : s ∈ Ioo a b := by
    simpa only [interior_Icc] using (mem_interior_iff_mem_nhds.mpr habmem)
  have hab : a < b := hsab.1.trans hsab.2
  have hAa : A < a := (habS ⟨le_rfl, hab.le⟩).1.1
  have hbB : b < B := (habS ⟨hab.le, le_rfl⟩).1.2
  have habK : γ '' Icc a b ⊆ interior K := by
    rintro _ ⟨z, hz, rfl⟩
    exact (habS hz).2
  obtain ⟨p, hpA, hpa⟩ := partition A a hAa.le
  obtain ⟨q, hqb, hqB⟩ := partition b B hbB.le
  have hstep : (p.last, b) ∈ R := by
    change p.last ≤ b ∧ ∃ c C, IsCompact C ∧
      γ '' Icc p.last b ⊆ interior C ∧ C ⊆ U c
    rw [hpa]
    exact ⟨hab.le, i, K, hK, habK, hKU⟩
  let p' := p.snoc b hstep
  have hconnect : p'.last = q.head := by
    rw [show p'.last = b from RelSeries.last_snoc p b hstep, hqb]
  let r := p'.smash q hconnect
  let j : Fin r.length := (Fin.last p.length).castAdd q.length
  have hja : r j.castSucc = a := by
    rw [show r j.castSucc = p' (Fin.last p.length).castSucc from
      RelSeries.smash_castAdd hconnect (Fin.last p.length)]
    exact (RelSeries.snoc_castSucc p b hstep (Fin.last p.length)).trans hpa
  have hjb : r j.succ = b := by
    rw [show r j.succ = p' (Fin.last p.length).succ from
      RelSeries.smash_succ_castAdd hconnect (Fin.last p.length)]
    simpa [p', RelSeries.last] using (RelSeries.last_snoc p b hstep)
  choose c C hC using fun i : Fin r.length ↦ (r.step i).2
  refine ⟨r.length, r, c, C, j, ?_, ?_, ?_, hC, ?_⟩
  · exact Fin.monotone_iff_le_succ.mpr (fun i ↦ (r.step i).1)
  · change r.head = A
    simpa only [r, RelSeries.head_smash, p', RelSeries.head_snoc] using hpA
  · change r.last = B
    simpa only [r, RelSeries.last_smash] using hqB
  · simpa only [hja, hjb] using And.intro hAa (And.intro hsab.1 (And.intro hsab.2 hbB))

end PoincareConjecture.M08
