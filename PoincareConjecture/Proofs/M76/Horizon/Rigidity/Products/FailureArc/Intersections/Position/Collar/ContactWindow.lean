import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.PairCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_open_collar_contact_window
    {E X ι : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {K rim : Set E} (hK : IsCompact K)
    {S R : Set X} {g : E → X} (hg : ContinuousOn g K) (hgi : InjOn g K)
    (hmap : MapsTo g K R)
    (hproper : ∀ x ∈ K, g x ∈ frontier R ↔ x ∈ rim)
    {height : E → ℝ} (hheight : Continuous height)
    {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (hzero : ∀ x ∈ K, height x = 0 ↔ x ∈ rim)
    (hboundary : ∀ x ∈ K ∩ rim, g x ∈ S →
      ∃ C : OriginalSurfacePairChart e S (g '' K) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hinterior : ∀ x ∈ K, height x ≤ b → x ∉ rim → g x ∈ S →
      Nonempty (OriginalSurfacePairChart e S (g '' K) (g x) false)) :
    ∃ W : Set X, IsOpen W ∧ g '' (K ∩ {x | height x ≤ c}) ⊆ W ∧
      g '' (K ∩ {x | height x = c}) ⊆ W ∩ interior R ∧
      ∀ y ∈ S, y ∈ g '' K → y ∈ W →
        (y ∈ interior R ∧ Nonempty (OriginalSurfacePairChart e S (g '' K) y false)) ∨
        ∃ C : OriginalSurfacePairChart e S (g '' K) y true,
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
  let core := K ∩ {x | b ≤ height x}
  have hcore : IsCompact core := hK.inter_right (isClosed_le continuous_const hheight)
  let W := (g '' core)ᶜ
  have hW : IsOpen W := (hcore.image_of_continuousOn (hg.mono inter_subset_left)).isClosed.isOpen_compl
  have hsmall (x : E) (hxK : x ∈ K) (hxc : height x ≤ c) : g x ∈ W := by
    rintro ⟨z, hz, heq⟩
    have hzx : z = x := hgi hz.1 hxK heq
    have hxb : b ≤ height x := hzx ▸ hz.2
    exact hcb.not_ge (hxb.trans hxc)
  have hint (x : E) (hxK : x ∈ K) (hxr : x ∉ rim) : g x ∈ interior R := by
    by_contra hn
    exact hxr ((hproper x hxK).mp ⟨subset_closure (hmap hxK), hn⟩)
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact hsmall x hx.1 hx.2
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨hsmall x hx.1 hx.2.le, hint x hx.1 ?_⟩
    intro hxr
    exact hc.ne' (hx.2.symm.trans ((hzero x hx.1).mpr hxr))
  · rintro y hyS ⟨x, hxK, rfl⟩ hyW
    by_cases hxr : x ∈ rim
    · exact Or.inr (hboundary x ⟨hxK, hxr⟩ hyS)
    · refine Or.inl ⟨hint x hxK hxr, hinterior x hxK ?_ hxr hyS⟩
      exact le_of_lt (lt_of_not_ge (fun h => hyW ⟨x, ⟨hxK, h⟩, rfl⟩))

end PoincareConjecture.M76
