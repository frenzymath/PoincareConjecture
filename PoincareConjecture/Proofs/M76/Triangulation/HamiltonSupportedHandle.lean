import PoincareConjecture.Proofs.M76.Triangulation.HamiltonTheoremOne
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonHandleBoundaryGluing
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartHomeomorph










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76





theorem exists_supported_chart_handle_step
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset (Fin 3)) (hhandle : HasHamiltonChartHandleStraightening E J)
    (p : OpenPartialHomeomorph (Fin 3 → ℝ) X) (d : OpenPartialHomeomorph X E)
    (hp : coordinateCylinder J ⊆ p.source) (hpd : p.target ⊆ d.source)
    {N : Set (Fin 3 → ℝ)} (hN : IsOpen N)
    (hfront : frontier (coordinateCylinder J) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn (p.trans d) ((p.trans d).source ∩ N)) :
    ∃ F : X ≃ₜ X,
      IsCompact (p '' (coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2)) ∧
      p '' (coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2) ⊆ p.target ∧
      EqOn F id (p '' (coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2))ᶜ ∧
      FinitePiecewiseAffineOn (d ∘ F ∘ p) (closedBall (0 : Fin 3 → ℝ) 1) ∧
      LocallyPiecewiseAffineOn (d ∘ F ∘ p)
        (((p.trans d).source ∩ N) ∩ handleTransverseStrip J) := by
  let e := p.trans d
  have hesource : coordinateCylinder J ⊆ e.source := by
    intro x hx
    exact ⟨hp hx, hpd (p.mapsTo (hp hx))⟩
  obtain ⟨A, hA, ⟨H⟩⟩ := hhandle e hesource N hN hfront hPL
  have hAradius (x : Fin 3 → ℝ) (hx : 2 ≤ ‖x‖) : A x = x := by
    have h := (H.prop 1).2.1 x hx
    simpa using h
  have hAcyl : EqOn A id ((coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J)) := by
    intro x hx
    have h := (H.prop 1).2.2 x hx
    simpa using h
  let K := coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : Fin 3 → ℝ) 2).inter_left (isClosed_coordinateCylinder J)
  have hKp : K ⊆ p.source := fun _ hx => hp hx.1
  have hAK : EqOn A id Kᶜ := by
    intro x hx
    by_cases hxcyl : x ∈ coordinateCylinder J
    · apply hAradius
      have hn : x ∉ closedBall (0 : Fin 3 → ℝ) 2 := fun h => hx ⟨hxcyl, h⟩
      exact (lt_of_not_ge (by simpa only [mem_closedBall_zero_iff] using hn)).le
    · exact hAcyl (Or.inl hxcyl)
  obtain ⟨F, hFp, hFout⟩ := p.exists_supported_chart_homeomorph A hK hKp hAK
  have hformula : EqOn (d ∘ F ∘ p) (e ∘ A) p.source := by
    intro x hx
    have h := hFp (p.mapsTo hx)
    change F (p x) = p (A (p.symm (p x))) at h
    rw [p.left_inv hx] at h
    exact congrArg d h
  have hcore : closedBall (0 : Fin 3 → ℝ) 1 ⊆ p.source := by
    intro x hx
    apply hp
    intro i _
    have hi := (pi_norm_le_iff_of_nonneg zero_le_one).mp
      (mem_closedBall_zero_iff.mp hx) i
    simpa only [Real.norm_eq_abs] using hi
  have hnewPL : LocallyPiecewiseAffineOn (e ∘ A)
      ((e.source ∩ N) ∩ handleTransverseStrip J) :=
    locallyPiecewiseAffineOn_handle_attaching_strip J hPL hA
      (fun x hx => congrArg e (hAcyl hx))
  refine ⟨F, hK.image_of_continuousOn (p.continuousOn_toFun.mono hKp),
    ?_, hFout, hA.congr (fun x hx => (hformula (hcore hx)).symm), ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact p.mapsTo (hKp hx)
  · exact hnewPL.congr (fun x hx => (hformula hx.1.1.1).symm)

end PoincareConjecture.M76
