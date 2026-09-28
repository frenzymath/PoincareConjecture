import PoincareConjecture.Statements.M15Noncollapsing











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



noncomputable def reducedVolumeLowerBound (n : ℕ) (taubar l₀ V : ℝ) : ℝ :=
  Real.rpow taubar (-(n : ℝ) / 2) * Real.exp (-l₀) * V



theorem reducedVolumeLowerBound_pos {taubar l₀ V : ℝ}
    (htaubar : 0 < taubar) (hV : 0 < V) :
    0 < reducedVolumeLowerBound n taubar l₀ V := by
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos htaubar _) (Real.exp_pos _)) hV




theorem stable_reducedLength_le_branch {T τ : ℝ} {x : G.Point}
    {E : M14ExponentialFamily G T x} (H : M14StableSet G T τ x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) ≤
      E.reduced_length Z (Real.sqrt τ) := by
  obtain ⟨p, _, hp, _⟩ := H.minimizing_path Z hZ
  have hbdd : BddBelow (M14ActionSet G T 0 τ x (H.endpoint_map Z)) := by
    refine ⟨M14BackwardLAction G p, ?_⟩
    rintro a ⟨q, rfl⟩
    exact hp q
  have hroot : 0 < Real.sqrt τ := Real.sqrt_pos.2 H.tau_pos
  have hpath : E.action Z (Real.sqrt τ) ∈
      M14ActionSet G T 0 (Real.sqrt τ ^ 2) x (E.gamma Z (Real.sqrt τ)) :=
    ⟨E.path Z (Real.sqrt τ) (H.survivor Z hZ) hroot,
      (E.action_eq Z (Real.sqrt τ) (H.survivor Z hZ) hroot).symm⟩
  rw [Real.sq_sqrt H.tau_pos.le, ← H.endpoint_map_eq Z hZ] at hpath
  have hinf := csInf_le hbdd hpath
  rw [E.reduced_length_eq Z (Real.sqrt τ) (H.survivor Z hZ) hroot]
  exact div_le_div_of_nonneg_right hinf (by positivity)

variable {T : ℝ} {x : (G.slices T).Point}
  {E : M14ExponentialFamily G T x.val} {taubar l₀ V r : ℝ}
  {K : SpacetimeInterval} {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
  {B : M15ActualBallCylinder G T x r K C}



theorem configuration_W_nonempty
    (D : M15Theorem81Configuration G T x E taubar l₀ V r K C B)
    (hV : 0 < V) : D.W.Nonempty := by
  by_contra hW
  have hempty : D.W = ∅ := Set.not_nonempty_iff_eq_empty.mp hW
  have hzero : ENNReal.ofReal V ≤ 0 := by
    simpa [hempty] using D.terminal_image_volume
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hV)) hzero



theorem configuration_reducedLength_le
    (D : M15Theorem81Configuration G T x E taubar l₀ V r K C B)
    {Z : G.Horizontal x.val} (hZ : Z ∈ D.W) :
    M14ReducedLengthValue G T 0 D.tau₀ x.val (D.stable.endpoint_map Z) ≤ l₀ :=
  (stable_reducedLength_le_branch D.stable (D.W_subset_stable hZ)).trans
    (D.normalized_reduced_length Z hZ)




theorem configuration_reducedVolume_lower_bound
    (hM14 : GeneralizedLGeometryTheory.{u} n)
    (D : M15Theorem81Configuration G T x E taubar l₀ V r K C B)
    (hl₀ : 0 ≤ l₀) (hV : 0 < V) :
    ∀ τ, 0 < τ → τ ≤ D.tau₀ →
      ∃ Hτ : M14StableSet G T τ x.val E,
        D.W ⊆ Hτ.carrier ∧
        ∃ Aτ : M14ReducedVolumeAnalyticData G T τ x.val E Hτ,
          reducedVolumeLowerBound n taubar l₀ V ≤
            M14ReducedVolumeOnAnalyticCarrier Aτ D.W := by
  obtain ⟨L⟩ := hM14.conclusion X time I G
  obtain ⟨S⟩ := L.reduced_volume_source
  obtain ⟨A₀⟩ := L.reduced_volume_analytic T D.tau₀ x.val E D.stable
  have hlower := S.terminal_W_lower_bound T taubar x.val E D.tau₀
    D.tau₀_pos D.tau₀_le D.stable A₀ D.W D.W_open
    (configuration_W_nonempty D hV) D.W_open.measurableSet D.W_subset_stable
    l₀ V hl₀ hV (fun Z hZ => configuration_reducedLength_le D hZ)
    D.terminal_image_volume
  have hpower : Real.rpow taubar (-(n : ℝ) / 2) ≤
      Real.rpow D.tau₀ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos D.tau₀_pos D.tau₀_le
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have huniform : reducedVolumeLowerBound n taubar l₀ V ≤
      Real.rpow D.tau₀ (-(n : ℝ) / 2) * Real.exp (-l₀) * V :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le) hV.le
  intro τ hτ hτ₀
  obtain ⟨Hτ, hW, Aτ, hA⟩ := hlower.2 τ hτ hτ₀
  exact ⟨Hτ, hW, Aτ, huniform.trans hA⟩

end PoincareConjecture.Proofs.M15
