import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSpherePairCharts
import Mathlib.Topology.IsLocalHomeomorph









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q3" => sphere (0 : V3) 1

theorem ChartwisePLSphere.locallyFlat_lift
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (e i).source)
    {p : V3 → X} (hp : IsLocalHomeomorph p)
    (l : C(Q3, V3)) (hli : Function.Injective l)
    (hl : ∀ x, p (l x) = (s.parametrization x : X)) :
    Nonempty (LocallyFlatTopologicalSphere (range l)) := by
  let : CompactSpace Q3 := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let b : Q3 ≃ₜ range l := (l.continuous.isClosedEmbedding hli).isEmbedding.toHomeomorph
  have hcompact : IsCompact (range l) := isCompact_range l.continuous
  have hpS : ∀ z ∈ range l, p z ∈ S := by
    rintro z ⟨x, rfl⟩
    rw [hl]
    exact (s.parametrization x).property
  have hpinj : InjOn p (range l) := by
    rintro z ⟨x, rfl⟩ w ⟨y, rfl⟩ heq
    rw [hl, hl] at heq
    exact congrArg l (s.parametrization.injective (Subtype.ext heq))
  refine ⟨⟨b, ?_⟩⟩
  intro z hz
  obtain ⟨B, hzB, hBp⟩ := hp z
  have hBeq : (B : V3 → X) = p := hBp.symm
  let T := p '' (range l \ B.source)
  have hT : IsClosed T :=
    ((hcompact.diff B.open_source).image hp.continuous).isClosed
  have hpzT : p z ∉ T := by
    rintro ⟨w, hw, heq⟩
    have hwz := hpinj hw.1 hz heq
    exact hw.2 (hwz.symm ▸ hzB)
  obtain ⟨C, hpzC, _, _, hplane⟩ := s.exists_pair_chart hcompat hcover (hpS z hz)
  let D := (B.restr (p ⁻¹' Tᶜ)).trans C
  have hsource : D.source = B.source ∩ p ⁻¹' Tᶜ ∩ B ⁻¹' C.source := by
    change B.source ∩ interior (p ⁻¹' Tᶜ) ∩ B ⁻¹' C.source = _
    rw [(hT.isOpen_compl.preimage hp.continuous).interior_eq]
  refine ⟨D, ?_, ?_⟩
  · rw [hsource]
    exact ⟨⟨hzB, hpzT⟩, hBeq.symm ▸ hpzC⟩
  · intro y hy
    rw [hsource] at hy
    have hmem : y ∈ range l ↔ p y ∈ S := by
      refine ⟨hpS y, ?_⟩
      intro hyp
      obtain ⟨x, hx⟩ := s.parametrization.surjective ⟨p y, hyp⟩
      have hpx : p (l x) = p y := (hl x).trans (congrArg Subtype.val hx)
      have hlxB : l x ∈ B.source := by
        by_contra hn
        exact hy.1.2 ⟨l x, ⟨mem_range_self x, hn⟩, hpx⟩
      have heq : l x = y := B.injOn hlxB hy.1.1 (by simpa only [hBeq] using hpx)
      exact ⟨x, heq⟩
    change y ∈ range l ↔ C (B y) 0 = 0
    exact hmem.trans (by simpa only [hBeq] using hplane (B y) hy.2)

end PoincareConjecture.M76
