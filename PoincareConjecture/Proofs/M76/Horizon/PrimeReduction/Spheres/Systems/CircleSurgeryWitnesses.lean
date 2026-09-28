import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1



theorem ChartwisePLSphere.exists_circle_cut_witness_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (d : Bool → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d true ∪ d false = Sphere) (hinter : d true ∩ d false = r)
    {M D O : Set X} (hSM : S ⊆ M) (hcap : D ∩ M = s.map '' r)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ (p : Bool → V3) (U : Set X),
      IsOpen U ∧ D ⊆ U ∧ U ⊆ O ∧
      s.map (p true) ≠ s.map (p false) ∧
      ∀ b, p b ∈ d b \ r ∧ s.map (p b) ∈ S ∧
        s.map (p b) ∉ D ∧ s.map (p b) ∉ U := by
  classical
  choose p hp using fun b => (hd b).isConnected_sdiff.nonempty
  have hdS (b : Bool) : d b ⊆ Sphere := by
    cases b
    · exact subset_union_right.trans hwhole.subset
    · exact subset_union_left.trans hwhole.subset
  have hrS : r ⊆ Sphere := (hd true).1.trans (hdS true)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hpS (b : Bool) : s.map (p b) ∈ S := by
    rw [s.map_eq ⟨p b,hdS b (hp b).1⟩]
    exact (s.parametrization ⟨p b,hdS b (hp b).1⟩).property
  have hpD (b : Bool) : s.map (p b) ∉ D := by
    intro hx
    obtain ⟨y,hy,heq⟩ := hcap.subset ⟨hx,hSM (hpS b)⟩
    have hyeq := hsi (hrS hy) (hdS b (hp b).1) heq
    exact (hp b).2 (hyeq ▸ hy)
  have hpne : s.map (p true) ≠ s.map (p false) := by
    intro h
    have heq := hsi (hdS true (hp true).1) (hdS false (hp false).1) h
    exact (hp true).2 (hinter.subset ⟨(hp true).1,heq.symm ▸ (hp false).1⟩)
  let U := O \ ({s.map (p true)} ∪ {s.map (p false)})
  refine ⟨p,U,hO.sdiff (isClosed_singleton.union isClosed_singleton),?_,
    sdiff_subset,hpne,?_⟩
  · intro x hx
    refine ⟨hDO hx,?_⟩
    rintro (heq | heq)
    · exact hpD true (mem_singleton_iff.mp heq ▸ hx)
    · exact hpD false (mem_singleton_iff.mp heq ▸ hx)
  · intro b
    refine ⟨hp b,hpS b,hpD b,?_⟩
    intro h
    cases b
    · exact h.2 (Or.inr rfl)
    · exact h.2 (Or.inl rfl)

private theorem retained_disk_excludes_joint_witnesses
    (d : Bool → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d true ∪ d false = Sphere) (hinter : d true ∩ d false = r)
    (p : Bool → V3) (hp : ∀ b, p b ∈ d b \ r)
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q)
    (hkS : k ⊆ Sphere) (hkr : Disjoint k r) :
    ¬ (p true ∈ k ∧ p false ∈ k) := by
  rintro ⟨hpt,hpf⟩
  have hconn := isPreconnected_closed_iff.mp hk.isConnected.isPreconnected
  obtain ⟨x,hxk,hxd⟩ := hconn (d true) (d false)
    (hd true).isCompact.isClosed (hd false).isCompact.isClosed
    (hkS.trans hwhole.symm.subset) ⟨p true,hpt,(hp true).1⟩
    ⟨p false,hpf,(hp false).1⟩
  exact Set.disjoint_left.mp hkr hxk (hinter.subset hxd)




theorem circle_cut_witnesses_meet_retained_disks
    {X : Type*} (f : V3 → X)
    (d : Bool → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d true ∪ d false = Sphere) (hinter : d true ∩ d false = r)
    (p : Bool → V3) (hp : ∀ b, p b ∈ d b \ r)
    {U : Set X} (houtside : ∀ b, f (p b) ∉ U)
    (k q : Bool → Set V3) (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b))
    (hkS : ∀ b, k b ⊆ Sphere) (hkr : ∀ b, Disjoint (k b) r)
    {band : Set V3} (hcover : (k true ∪ k false) ∪ band = Sphere)
    (hqband : ∀ b, q b ⊆ band) (hbandU : f '' band ⊆ U) :
    ∀ b, ∃ i : Bool, p i ∈ k b \ q b ∧ f (p i) ∉ U := by
  have hdS (b : Bool) : d b ⊆ Sphere := by
    cases b
    · exact subset_union_right.trans hwhole.subset
    · exact subset_union_left.trans hwhole.subset
  have hpband (b : Bool) : p b ∉ band :=
    fun hx => houtside b (hbandU ⟨p b,hx,rfl⟩)
  have hpk (b : Bool) : p b ∈ k true ∪ k false := by
    have h := hcover.symm.subset (hdS b (hp b).1)
    exact h.resolve_right (hpband b)
  have hnotboth (b : Bool) : ¬ (p true ∈ k b ∧ p false ∈ k b) :=
    retained_disk_excludes_joint_witnesses d hd hwhole hinter p hp
      (hk b) (hkS b) (hkr b)
  have hsome (b : Bool) : ∃ i : Bool, p i ∈ k b := by
    cases b
    · rcases hpk true with ht | ht
      · exact ⟨false,(hpk false).resolve_left (fun hf => hnotboth true ⟨ht,hf⟩)⟩
      · exact ⟨true,ht⟩
    · rcases hpk true with ht | ht
      · exact ⟨true,ht⟩
      · exact ⟨false,(hpk false).resolve_right (fun hf => hnotboth false ⟨ht,hf⟩)⟩
  intro b
  obtain ⟨i,hi⟩ := hsome b
  exact ⟨i,⟨hi,fun hq => hpband i (hqband b hq)⟩,houtside i⟩

end PoincareConjecture.M76
