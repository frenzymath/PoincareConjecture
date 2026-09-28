import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCollarStrip
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeCollarCoreGeometry
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeCoreRetraction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import Mathlib.Topology.Connected.Basic










set_option autoImplicit false

open Set

variable {E X : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
  [TopologicalSpace X] [T2Space X]



theorem compact_collar_core {B : Set E} {K : Set X}
    (hK : IsCompact K) (hconnected : IsConnected K)
    (hB : IsCompact B) (hBne : B.Nonempty)
    (HB : B ≃ₜ frontier K) (c : E × ℝ → X)
    (hc : ContinuousOn c (B ×ˢ Icc 0 1))
    (hi : Topology.IsEmbedding (fun z : (B ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (B ×ˢ Icc 0 1) K)
    (hbase : ∀ z : B, c ((z : E), 0) = HB z)
    (hproper : ∀ z : (B ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)),
      c z ∈ frontier K ↔ (z : E × ℝ).2 = 0)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ1 : δ ≤ 1)
    (hopen : IsOpen ((Subtype.val : K → X) ⁻¹' (c '' (B ×ˢ Ico 0 ε)))) :
    IsCompact (K \ (c '' (B ×ˢ Ico 0 ε))) ∧
      IsConnected (K \ (c '' (B ×ˢ Ico 0 ε))) ∧
      interior (K \ (c '' (B ×ˢ Ico 0 ε))) =
        interior K \ (c '' (B ×ˢ Icc 0 ε)) ∧
      frontier (K \ (c '' (B ×ˢ Ico 0 ε))) = c '' (B ×ˢ {ε}) ∧
      K \ (c '' (B ×ˢ Ico 0 ε)) ⊆ interior K ∧
      (c '' (B ×ˢ Icc 0 ε)) ∩ (K \ (c '' (B ×ˢ Ico 0 ε))) = c '' (B ×ˢ {ε}) ∧
      (c '' (B ×ˢ Icc 0 ε)) ∪ (K \ (c '' (B ×ˢ Ico 0 ε))) = K ∧
      (interior (K \ (c '' (B ×ˢ Ico 0 ε)))).Nonempty ∧
      ∃ r : K → X, Continuous r ∧ range r = K \ (c '' (B ×ˢ Ico 0 ε)) ∧
        ∀ x : K, (x : X) ∈ K \ (c '' (B ×ˢ Ico 0 ε)) → r x = x := by
  have hε1 : ε ≤ 1 := hεδ.le.trans hδ1
  have hinj : InjOn c (B ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw heq
    have h : (⟨z, hz⟩ : (B ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ))) = ⟨w, hw⟩ :=
      hi.injective heq
    exact congrArg Subtype.val h
  obtain ⟨hN, hNK, hUN, hclosure, hlevel, hfront⟩ :=
    compact_collar_strip_geometry hB HB c hc hinj hinside hbase hε hε1
  obtain ⟨hC, hint, hfrontC, hCint, hmeet, hcover⟩ :=
    relative_collar_core_geometry hK hNK hUN hopen hclosure hlevel hfront
  have hsub : B ×ˢ Icc (0 : ℝ) ε ⊆ B ×ˢ Icc 0 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hε1⟩
  have hNfull : c '' (B ×ˢ Icc 0 ε) ⊆ c '' (B ×ˢ Icc 0 1) := image_mono hsub
  obtain ⟨k, hk, hleft, _, hkbounds⟩ := hi.exists_inverse_on_image
  let r0 : X → X := fun x => c ((k x).1, ε)
  have hr0 : ContinuousOn r0 (c '' (B ×ˢ Icc 0 ε)) := by
    apply hc.comp ((hk.mono hNfull).fst.prodMk continuousOn_const)
    intro x hx
    exact ⟨(hkbounds (hNfull hx)).1, hε.le, hε1⟩
  have hrmap : MapsTo r0 (c '' (B ×ˢ Icc 0 ε)) (c '' (B ×ˢ {ε})) := by
    intro x hx
    exact ⟨((k x).1, ε), ⟨(hkbounds (hNfull hx)).1, rfl⟩, rfl⟩
  have hrfix : EqOn r0 id (c '' (B ×ˢ {ε})) := by
    rintro x ⟨z, hz, rfl⟩
    have ht : z.2 = ε := mem_singleton_iff.mp hz.2
    have hzI : z ∈ B ×ˢ Icc (0 : ℝ) 1 := by
      refine ⟨hz.1, ?_⟩
      rw [ht]
      exact ⟨hε.le, hε1⟩
    change c ((k (c z)).1, ε) = c z
    rw [hleft z hzI]
    exact congrArg c (Prod.ext rfl ht.symm)
  obtain ⟨r, hr, hrange, hfix⟩ := exists_relative_core_retraction
    hN.isClosed hNK hUN hopen hlevel r0 hr0 hrmap hrfix
  have hCconnected : IsConnected (K \ (c '' (B ×ˢ Ico 0 ε))) := by
    let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hconnected
    rw [← hrange]
    exact isConnected_range hr
  refine ⟨hC, hCconnected, hint, hfrontC, hCint, hmeet, hcover, ?_, r, hr, hrange, hfix⟩
  obtain ⟨z, hz⟩ := hBne
  have hzI : (z, δ) ∈ B ×ˢ Icc (0 : ℝ) 1 := ⟨hz, (hε.trans hεδ).le, hδ1⟩
  have hzint : c (z, δ) ∈ interior K := by
    apply (mem_interior_iff_notMem_frontier (hinside hzI)).mpr
    intro h
    have heq := (hproper ⟨(z, δ), hzI⟩).mp h
    exact (hε.trans hεδ).ne' heq
  have hznot : c (z, δ) ∉ c '' (B ×ˢ Icc 0 ε) := by
    rintro ⟨w, hw, heq⟩
    have hwz : w = (z, δ) := hinj (hsub hw) hzI heq
    have ht : w.2 = δ := congrArg Prod.snd hwz
    exact (not_le_of_gt hεδ) (ht ▸ hw.2.2)
  refine ⟨c (z, δ), ?_⟩
  rw [hint]
  exact ⟨hzint, hznot⟩
