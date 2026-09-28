import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FrontierCrossingTransport







set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem paired_crossing_chart_in_compatible_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S F : Set X}
    (Q₀ Q : OpenPartialHomeomorph X V3)
    (hQ₀ : ∀ i, (e i).symm.trans Q₀ ∈ piecewiseAffineGroupoid V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {y : X} (hycover : ∃ i, y ∈ (e i).source)
    (hyQ₀ : y ∈ Q₀.source) (hyQ : y ∈ Q.source)
    (B : OpenPartialHomeomorph V3 C3) (hyB : Q₀ y ∈ B.source)
    (hB0 : B (Q₀ y) = 0)
    (hB : LocallyPiecewiseAffineOn B B.source)
    (hBi : LocallyPiecewiseAffineOn B.symm B.target)
    (hBS : ∀ x ∈ B.source, Q₀.symm x ∈ S ↔ (B x).2 = 0)
    (hBF : ∀ x ∈ B.source, Q₀.symm x ∈ F ↔ (B x).1.1 = 0)
    {O : Set V3} (hO : IsOpen O) (hyO : Q y ∈ O) :
    ∃ C : OpenPartialHomeomorph V3 C3,
      Q y ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧ C (Q y) = 0 ∧
      LocallyPiecewiseAffineOn C C.source ∧ LocallyPiecewiseAffineOn C.symm C.target ∧
      (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
      ∀ x ∈ C.source, Q.symm x ∈ F ↔ (C x).1.1 = 0 := by
  obtain ⟨i,hyi⟩ := hycover
  let T := ((e i).symm.trans Q).symm.trans ((e i).symm.trans Q₀)
  have hT : T ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm (hQ i)) (hQ₀ i)
  have hyT : Q y ∈ T.source := by
    change (Q y ∈ Q.target ∧ Q.symm (Q y) ∈ (e i).source) ∧
      (e i (Q.symm (Q y)) ∈ (e i).target ∧ (e i).symm (e i (Q.symm (Q y))) ∈ Q₀.source)
    simpa only [Q.left_inv hyQ,(e i).left_inv hyi] using
      And.intro (And.intro (Q.map_source hyQ) hyi) (And.intro ((e i).map_source hyi) hyQ₀)
  have hTval (x : V3) (hx : x ∈ T.source) : T x = Q₀ (Q.symm x) := by
    change Q₀ ((e i).symm (e i (Q.symm x))) = Q₀ (Q.symm x)
    rw [(e i).left_inv hx.1.2]
  have hback (x : V3) (hx : x ∈ T.source) : Q.symm x ∈ Q₀.source := by
    have hh := hx.2.2
    change (e i).symm (e i (Q.symm x)) ∈ Q₀.source at hh
    rwa [(e i).left_inv hx.1.2] at hh
  have hTy : T (Q y) = Q₀ y := by rw [hTval _ hyT,Q.left_inv hyQ]
  let D := T.trans B
  have hD : LocallyPiecewiseAffineOn D D.source := hB.comp hT.1
  have hDi : LocallyPiecewiseAffineOn D.symm D.target := hT.2.comp hBi
  let C := D.restrOpen O hO
  have hC : LocallyPiecewiseAffineOn C C.source := hD.mono C.open_source inter_subset_left
  have hCi : LocallyPiecewiseAffineOn C.symm C.target := hDi.mono C.open_target inter_subset_left
  have hyC : Q y ∈ C.source := ⟨⟨hyT,by change T (Q y) ∈ B.source; rwa [hTy]⟩,hyO⟩
  refine ⟨C,hyC,(fun x hx => ⟨hx.2,hx.1.1.1.1⟩),?_,hC,hCi,?_,?_⟩
  · change B (T (Q y)) = 0
    rwa [hTy]
  · intro x hx
    have hh := hBS (T x) hx.1.2
    rw [hTval x hx.1.1,Q₀.left_inv (hback x hx.1.1)] at hh
    change Q.symm x ∈ S ↔ (B (T x)).2 = 0
    rw [hTval x hx.1.1]
    exact hh
  · intro x hx
    have hh := hBF (T x) hx.1.2
    rw [hTval x hx.1.1,Q₀.left_inv (hback x hx.1.1)] at hh
    change Q.symm x ∈ F ↔ (B (T x)).1.1 = 0
    rw [hTval x hx.1.1]
    exact hh

end PoincareConjecture.M76
