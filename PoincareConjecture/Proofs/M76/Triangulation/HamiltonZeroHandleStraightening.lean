import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroCappedAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroProtectedBall
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroProtectedCoreConstruction
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedHandleComparison
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedAtlasCorrection











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "Y" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set W)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "R" => latticeHandleDomain (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 0 ↪ Fin 0 ⊕ Fin 3)
local notation "D" => coordinateCylinder J
local notation "pi" => latticeCoordinateProjection (Fin 0) (Fin 3) hamiltonZeroPeriodLattice




instance hamiltonZeroLatticeHandleT2 : T2Space W := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  exact hamiltonZeroHandleProductEquiv.isEmbedding.t2Space






theorem exists_hamilton_zero_handle_straightening
    (h : OpenPartialHomeomorph CubeShell.Ambient V3) (hsource : h.source = univ)
    (wall : ∀ e : Y → OpenPartialHomeomorph Y V3, HasWallCompactCore e)
    (brown : HasBrownLocallyFlatSphereBalls)
    (prime : ∀ charts : Set (OpenPartialHomeomorph W V3),
      HasHamiltonProtectedIrreducibleReplacement (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
        (fun c : charts => (c : OpenPartialHomeomorph W V3)))
    (approximation : ∀ (charts : Set (OpenPartialHomeomorph W V3))
      (d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph W V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph W V3)) d R)
    (rigidity : ∀ (charts : Set (OpenPartialHomeomorph W V3))
      (d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph W V3),
      HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
        (fun c : charts => (c : OpenPartialHomeomorph W V3)) d) :
    ∃ B : V ≃ₜ V,
      FinitePiecewiseAffineOn
        ((fun x : V => h (CubeShell.vector (fun j => x (Sum.inr j)))) ∘ B)
        (closedBall (0 : V) 1) ∧
      Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id V) ⟨B, B.continuous⟩
        (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
          ∀ x ∈ Dᶜ ∪ frontier D, f x = x)) := by
  classical
  obtain ⟨d, charts, hd, he, r, c, hr, hr64, hretained⟩ :=
    exists_zero_lattice_capped_PL_domain h hsource wall brown
  let e : charts → OpenPartialHomeomorph W V3 := fun i => i
  let origin : W := (0, QuotientAddGroup.mk (0 : V3))
  have horigin : origin ∈ (e c).source :=
    (hretained 0 (by simpa only [norm_zero] using hr.le)).1
  obtain ⟨P0, hP0origin, hP0ball⟩ :=
    exists_hamilton_zero_protected_chart_ball e c origin horigin
  have hR : R = univ := by
    ext y
    have hy : y.1 = 0 := Subsingleton.elim _ _
    simp [latticeHandleDomain, hy]
  have hempty : ChartwisePLOn e d (ContinuousMap.id R) ∅ := {
    source_domain := he
    target_domain := hd.domain
    open_domain := isOpen_empty
    coordinates := by intro x hx; exact False.elim hx }
  obtain ⟨replacement, N, hN, hP0N, _, _, hback, g, hgPL,
    G, hG, _, _, _, _, p, hps, _, hpcore, _, _, hpiPL, A, hA, ⟨HA⟩⟩ :=
    exists_hamilton_protected_handle_comparison (Fin 0) (Fin 3)
      hamiltonZeroPeriodLattice e d (by simp) (by simp) he hd (prime charts)
      (fun replacement => approximation replacement d)
      (fun replacement => rigidity replacement d) P0 hP0ball ∅
      (by simp [hR]) hempty (r := 3 / 2) (by norm_num) (by norm_num)
  let e' : replacement → OpenPartialHomeomorph W V3 := fun i => i
  have hpi : Continuous pi :=
    (continuous_pi fun i => continuous_apply (Sum.inl i)).prodMk
      (QuotientAddGroup.continuous_mk.comp
        (continuous_pi fun i => continuous_apply (Sum.inr i)))
  have hpi0 : pi (0 : V) = origin := rfl
  let P : Set V := ball 0 r ∩ pi ⁻¹' N
  have hopen : IsOpen P := isOpen_ball.inter (hN.preimage hpi)
  have hPzero : (0 : V) ∈ interior P := by
    rw [hopen.interior_eq]
    refine ⟨mem_ball_self hr, ?_⟩
    change pi (0 : V) ∈ N
    rw [hpi0]
    exact hP0N (Or.inl hP0origin)
  have hPC : P ⊆ closedBall (0 : V) 1 := by
    intro x hx
    have hxnorm : ‖x‖ < r := mem_ball_zero_iff.mp hx.1
    exact mem_closedBall_zero_iff.mpr (by linarith)
  have hfree (x : V) : ‖fun j : Fin 3 => x (Sum.inr j)‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    exact fun j => norm_le_pi_norm x (Sum.inr j)
  have hpisplit (x : V) : pi x =
      (0, QuotientAddGroup.mk (fun j : Fin 3 => x (Sum.inr j))) := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  let original : V → V3 := fun x => h (CubeShell.vector (fun j => x (Sum.inr j)))
  have hchart (x : V) (hx : x ∈ P) : pi x ∈ (e c).source := by
    rw [hpisplit]
    exact (hretained _ ((hfree x).trans (mem_ball_zero_iff.mp hx.1).le)).1
  have hformula (x : V) (hx : x ∈ P) :
      original x = (ContinuousAffineMap.id ℝ V3) (e c (pi x)) := by
    change h (CubeShell.vector (fun j => x (Sum.inr j))) = e c (pi x)
    rw [hpisplit]
    exact (hretained _ ((hfree x).trans (mem_ball_zero_iff.mp hx.1).le)).2.symm
  have hAout (x : V) (hx : 2 ≤ ‖x‖) : A x = x := by
    have hfix := (HA.prop 1).2.1 x hx
    change HA (1, x) = x at hfix
    rwa [HA.apply_one] at hfix
  have hArel (x : V) (hx : x ∈ Dᶜ ∪ frontier D) : A x = x := by
    have hfix := (HA.prop 1).2.2 x hx
    change HA (1, x) = x at hfix
    rwa [HA.apply_one] at hfix
  obtain ⟨data, hdata⟩ := exists_hamiltonProtectedCoreData_zero_marked
    original e d hd p hps hpcore hpiPL A G hA hAout P hPC hPzero c
      (ContinuousAffineMap.id ℝ V3) hchart hformula
  obtain ⟨B, _, hB, hBH⟩ := lowerHandleStraightening_of_protected_atlas_comparison
    original e e' d ((Subtype.val : R → W) ⁻¹' N) hback g hgPL G hG
      p hps A hA hAout hArel data (by
        intro x hx
        rw [hdata] at hx
        exact hx.2)
  exact ⟨B, hB, hBH⟩

end PoincareConjecture.M76
