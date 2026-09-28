import PoincareConjecture.Proofs.M76.Mathlib.PLInCharts

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F G H X Y Z W ι κ nu μ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

namespace PLInCharts

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ H] in

theorem prodMap {Q : ι → OpenPartialHomeomorph E X}
    {R : κ → OpenPartialHomeomorph F Y} {S : nu → OpenPartialHomeomorph G Z}
    {T : μ → OpenPartialHomeomorph H W} {f : X → Y} {g : Z → W}
    {U : Set X} {V : Set Z} (hf : PLInCharts Q R f U) (hg : PLInCharts S T g V) :
    PLInCharts (fun i : ι × nu => (Q i.1).prod (S i.2))
      (fun j : κ × μ => (R j.1).prod (T j.2)) (Prod.map f g) (U ×ˢ V) := by
  refine ⟨hf.isOpen.prod hg.isOpen, hf.continuousOn.prodMap hg.continuousOn, ?_⟩
  intro i j
  have hPL := (hf.coordinates i.1 j.1).prodMap (hg.coordinates i.2 j.2)
  have hdom : chartMapDomain ((Q i.1).prod (S i.2)) ((R j.1).prod (T j.2))
      (Prod.map f g) (U ×ˢ V) =
      chartMapDomain (Q i.1) (R j.1) f U ×ˢ chartMapDomain (S i.2) (T j.2) g V := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨⟨hz.1.1.1, hz.1.2.1⟩, hz.2.1⟩,
        ⟨⟨hz.1.1.2, hz.1.2.2⟩, hz.2.2⟩⟩
    · intro hz
      exact ⟨⟨⟨hz.1.1.1, hz.2.1.1⟩, ⟨hz.1.1.2, hz.2.1.2⟩⟩, ⟨hz.1.2, hz.2.2⟩⟩
  rw [hdom]
  exact hPL

omit [FiniteDimensional ℝ F] in

theorem locality {Q : ι → OpenPartialHomeomorph E X}
    {R : κ → OpenPartialHomeomorph F Y} {f : X → Y} {U : Set X}
    (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ PLInCharts Q R f (U ∩ V)) :
    PLInCharts Q R f U := by
  have hcont : ContinuousOn f U := continuousOn_of_locally_continuousOn
    (fun x hx => by
      obtain ⟨V, hV, hxV, hPL⟩ := hlocal x hx
      exact ⟨V, hV, hxV, hPL.continuousOn⟩)
  refine ⟨hU, hcont, ?_⟩
  intro i j
  have hD := isOpen_chartMapDomain (Q i) (R j) f U hU hcont
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨V, hV, hxV, hPL⟩ := hlocal (Q i x) hx.1.2
  let A := (Q i).source ∩ (Q i) ⁻¹' V
  have hA : IsOpen A :=
    (Q i).continuousOn_toFun.isOpen_inter_preimage (Q i).open_source hV
  refine ⟨A, ⟨hx.1.1, hxV⟩, ?_⟩
  exact (hPL.coordinates i j).mono (hD.inter hA)
    (fun _ hy => ⟨⟨hy.1.1.1, ⟨hy.1.1.2, hy.2.2⟩⟩, hy.1.2⟩)

omit [FiniteDimensional ℝ F] in

theorem union {Q : ι → OpenPartialHomeomorph E X}
    {R : κ → OpenPartialHomeomorph F Y} {f : X → Y} {U V : Set X}
    (hU : PLInCharts Q R f U) (hV : PLInCharts Q R f V) :
    PLInCharts Q R f (U ∪ V) := by
  apply locality (hU.isOpen.union hV.isOpen)
  intro x hx
  rcases hx with hx | hx
  · exact ⟨U, hU.isOpen, hx,
      hU.mono ((hU.isOpen.union hV.isOpen).inter hU.isOpen) inter_subset_right⟩
  · exact ⟨V, hV.isOpen, hx,
      hV.mono ((hU.isOpen.union hV.isOpen).inter hV.isOpen) inter_subset_right⟩

end PLInCharts

end Geometry
