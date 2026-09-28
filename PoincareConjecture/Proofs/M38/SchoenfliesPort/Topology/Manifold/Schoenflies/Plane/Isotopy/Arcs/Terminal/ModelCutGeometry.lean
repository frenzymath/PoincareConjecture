import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCapCircles
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelUpperCircle
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelRegularWindow
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.LowerComponentDisks
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.UpperComponentDisk







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}


structure ModelCutCircleData (d : TerminalSaddleGeometry M P p e) (η : Real) where
  cut_pos : 0 < η
  lower : Fin 2 → S1 → S2
  upper : S1 → S2
  separator : S2 → Real
  height_smooth : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
    (fun q : S2 => inner Real (M.v : E3) (d.filledModel q))
  height_center : inner Real (M.v : E3) (d.filledModel (d.modelChart 0)) =
    inner Real (M.v : E3) (g p)
  lower_smooth : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (lower i)
  lower_injective : ∀ i, Injective (lower i)
  lower_derivative : ∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (lower i) q)
  lower_level : {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
    inner Real (M.v : E3) (g p) - η} = range (lower 0) ∪ range (lower 1)
  separator_continuous : Continuous separator
  separator_nonzero : ∀ q : S2, inner Real (M.v : E3) (d.filledModel q) ≤
    inner Real (M.v : E3) (g p) - η → separator q ≠ 0
  lower_negative : ∀ q, separator (lower 0 q) < 0
  lower_positive : ∀ q, 0 < separator (lower 1 q)
  upper_smooth : ContMDiff (𝓡 1) (𝓡 2) ∞ upper
  upper_injective : Injective upper
  upper_derivative : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) upper q)
  upper_level : {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
    inner Real (M.v : E3) (g p) + η} = range upper
  lower_regular : ∀ q : S2, inner Real (M.v : E3) (d.filledModel q) =
    inner Real (M.v : E3) (g p) - η →
    mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) q ≠ 0
  upper_regular : ∀ q : S2, inner Real (M.v : E3) (d.filledModel q) =
    inner Real (M.v : E3) (g p) + η →
    mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) q ≠ 0



theorem exists_terminal_model_cut_circle_data
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ η ∈ Ioc (0 : Real) ε,
      Nonempty (ModelCutCircleData d η) := by
  obtain ⟨εₗ, hεₗ, hlower⟩ := exists_model_lower_separated_source_circle_pair d hform
  obtain ⟨εᵤ, hεᵤ, hupper⟩ := exists_model_upper_source_circles d hform
  obtain ⟨εᵣ, hεᵣ, hregular⟩ := exists_terminal_model_regular_window d hform
  obtain ⟨hh, hc, _⟩ := terminal_physical_model_central_level_facts d hform
  refine ⟨min εₗ (min εᵤ εᵣ), lt_min hεₗ (lt_min hεᵤ hεᵣ), ?_⟩
  intro η hη
  have hηl : η ≤ εₗ := hη.2.trans (min_le_left _ _)
  have hηu : η ≤ εᵤ := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηr : η ≤ εᵣ := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C, l, hC, hCi, hCd, hCl, hl, hlz, hln, hlp⟩ := hlower η ⟨hη.1, hηl⟩
  obtain ⟨B, hB, hBi, hBd, hBl⟩ := hupper η ⟨hη.1, hηu⟩
  refine ⟨{
    cut_pos := hη.1
    lower := C, upper := B, separator := l
    height_smooth := hh, height_center := hc
    lower_smooth := hC, lower_injective := hCi, lower_derivative := hCd
    lower_level := hCl, separator_continuous := hl, separator_nonzero := hlz
    lower_negative := hln, lower_positive := hlp
    upper_smooth := hB, upper_injective := hBi, upper_derivative := hBd
    upper_level := hBl.symm
    lower_regular := ?_, upper_regular := ?_ }⟩
  · intro q hq
    apply hregular (-η) ⟨by linarith, by linarith [hεᵣ, hη.1]⟩ (by linarith [hη.1]) q
    simpa only [sub_eq_add_neg] using hq
  · intro q hq
    exact hregular η ⟨by linarith [hεᵣ, hη.1], hηr⟩ hη.1.ne' q hq


def ModelCutCircleData.boundaryCircle {d : TerminalSaddleGeometry M P p e} {η : Real}
    (a : ModelCutCircleData d η) : Fin 3 → S1 → S2 := ![a.lower 0, a.lower 1, a.upper]



structure ModelCutDiskData (d : TerminalSaddleGeometry M P p e) (η : Real)
    (a : ModelCutCircleData d η) where
  seed : Fin 3 → S2
  chart : Fin 3 → OpenPartialHomeomorph E2 S2
  seed_lower : ∀ i : Fin 2, inner Real (M.v : E3) (d.filledModel (seed i.castSucc)) <
    inner Real (M.v : E3) (g p) - η
  seed_upper : inner Real (M.v : E3) (g p) + η <
    inner Real (M.v : E3) (d.filledModel (seed 2))
  source : ∀ i, closedBall 0 1 ⊆ (chart i).source
  smooth : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chart i) (chart i).source
  inverse_smooth : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chart i).symm (chart i).target
  closed_component : ∀ i, chart i '' closedBall 0 1 = closure (connectedComponentIn
    {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉
      Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η)} (seed i))
  open_component : ∀ i, chart i '' ball 0 1 = connectedComponentIn
    {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉
      Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η)} (seed i)
  boundary : ∀ i, chart i '' sphere (0 : E2) 1 = range (a.boundaryCircle i)
  disjoint : ∀ i j, i ≠ j → Disjoint (chart i '' closedBall 0 1) (chart j '' closedBall 0 1)
  cover : (⋃ i, chart i '' ball 0 1) =
    {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉
      Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η)}



theorem ModelCutCircleData.exists_disks {d : TerminalSaddleGeometry M P p e} {η : Real}
    (a : ModelCutCircleData d η) : Nonempty (ModelCutDiskData d η a) := by
  let h : S2 → Real := fun q => inner Real (M.v : E3) (d.filledModel q)
  let c := inner Real (M.v : E3) (g p)
  have hab : c - η ≤ c + η := by linarith [a.cut_pos]
  obtain ⟨pₗ, mₗ, hmₗ, _, _, _, _, hdis, hclosed, hopen⟩ :=
    exists_lower_component_disks_of_separated_circle_pair a.height_smooth a.lower_regular
      a.lower a.lower_smooth a.lower_injective a.lower_derivative a.lower_level
      a.separator a.separator_continuous a.separator_nonzero a.lower_negative a.lower_positive
      ⟨d.modelChart 0, by rw [a.height_center]; linarith [a.cut_pos]⟩
  obtain ⟨pᵤ, hpᵤ, mᵤ, hsu, hmu, hmiu, hcu, hbu, hsu', hcompu⟩ :=
    exists_full_superlevel_disk_of_regular_circle_level a.height_smooth a.upper_regular
      a.upper_smooth a.upper_injective a.upper_derivative a.upper_level
  have hupperconn : IsPreconnected (h ⁻¹' Ioi (c + η)) := by
    rw [show h ⁻¹' Ioi (c + η) = mᵤ '' ball 0 1 from hbu.symm]
    exact isPreconnected_ball.image mᵤ (mᵤ.continuousOn.mono (ball_subset_closedBall.trans hsu))
  have huppercomp : connectedComponentIn (h ⁻¹' Ioi (c + η)) pᵤ = h ⁻¹' Ioi (c + η) :=
    (connectedComponentIn_subset _ _).antisymm
      (hupperconn.subset_connectedComponentIn hpᵤ Subset.rfl)
  have hbelow (i : Fin 2) : inner Real (M.v : E3) (d.filledModel (pₗ i)) < c - η := (hmₗ i).1
  have hlowcomp (i : Fin 2) := outside_height_band_component_eq_sublevel
    a.height_smooth.continuous hab (hbelow i)
  have huppcomp := outside_height_band_component_eq_superlevel
    a.height_smooth.continuous hab hpᵤ
  have hdisu (i : Fin 2) : Disjoint (mₗ i '' closedBall 0 1) (mᵤ '' closedBall 0 1) := by
    rw [Set.disjoint_left]
    intro q hql hqu
    have hql' : q ∈ mₗ 0 '' closedBall 0 1 ∪ mₗ 1 '' closedBall 0 1 := by
      fin_cases i
      · exact Or.inl hql
      · exact Or.inr hql
    have hhq : h q ≤ c - η := hclosed.subset hql'
    have hqh : c + η ≤ h q := hcu.subset hqu
    linarith [a.cut_pos]
  refine ⟨{
    seed := ![pₗ 0, pₗ 1, pᵤ], chart := ![mₗ 0, mₗ 1, mᵤ]
    seed_lower := ?_, seed_upper := hpᵤ
    source := ?_, smooth := ?_, inverse_smooth := ?_
    closed_component := ?_, open_component := ?_, boundary := ?_
    disjoint := ?_, cover := ?_ }⟩
  · intro i
    fin_cases i <;> exact hbelow _
  · intro i
    fin_cases i
    · exact (hmₗ 0).2.1
    · exact (hmₗ 1).2.1
    · exact hsu
  · intro i
    fin_cases i
    · exact (hmₗ 0).2.2.1
    · exact (hmₗ 1).2.2.1
    · exact hmu
  · intro i
    fin_cases i
    · exact (hmₗ 0).2.2.2.1
    · exact (hmₗ 1).2.2.2.1
    · exact hmiu
  · intro i
    fin_cases i
    · exact (hmₗ 0).2.2.2.2.1.trans (congrArg closure (hlowcomp 0).symm)
    · exact (hmₗ 1).2.2.2.2.1.trans (congrArg closure (hlowcomp 1).symm)
    · exact hcompu.trans (congrArg closure huppcomp.symm)
  · intro i
    fin_cases i
    · exact (hmₗ 0).2.2.2.2.2.1.trans (hlowcomp 0).symm
    · exact (hmₗ 1).2.2.2.2.2.1.trans (hlowcomp 1).symm
    · exact hbu.trans (huppercomp.symm.trans huppcomp.symm)
  · intro i
    fin_cases i
    · exact (hmₗ 0).2.2.2.2.2.2
    · exact (hmₗ 1).2.2.2.2.2.2
    · exact hsu'
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | exact hdis | exact hdis.symm |
      exact hdisu 0 | exact hdisu 1 | exact (hdisu 0).symm | exact (hdisu 1).symm
  · have hunion : (⋃ i : Fin 3, ![mₗ 0, mₗ 1, mᵤ] i '' ball 0 1) =
        (mₗ 0 '' ball 0 1) ∪ (mₗ 1 '' ball 0 1) ∪ (mᵤ '' ball 0 1) := by
      ext q
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr hi)
        · exact Or.inr hi
      · rintro ((h₀ | h₁) | h₂)
        · exact ⟨0, h₀⟩
        · exact ⟨1, h₁⟩
        · exact ⟨2, h₂⟩
    rw [hunion, hopen, hbu]
    ext q
    simp only [mem_union, mem_preimage, mem_Iio, mem_ofPred_eq, mem_Icc, not_and_or, not_le]



theorem exists_terminal_model_cut_disks
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ η ∈ Ioc (0 : Real) ε,
      ∃ a : ModelCutCircleData d η, Nonempty (ModelCutDiskData d η a) := by
  obtain ⟨ε, hε, hdata⟩ := exists_terminal_model_cut_circle_data d hform
  refine ⟨ε, hε, fun η hη => ?_⟩
  obtain ⟨a⟩ := hdata η hη
  exact ⟨a, a.exists_disks⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
