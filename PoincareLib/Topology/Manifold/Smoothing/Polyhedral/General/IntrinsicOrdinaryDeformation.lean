import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.AlexanderRecursiveCutSide
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Isotopy.ProtectedOrdinaryCappedIsotopy
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.OrdinaryCappedLevelComparisons

/-!
# Ordinary capped deformation from actual recursive collar geometry

The actual collar selects a cut side and supplies the protected
ordinary isotopy. A compact rim roof minimum gives one common
time for its exact birth levels and remainder comparisons.
No generic triangulation of the surface is used.
See Alexander 1924, p. 7 and M76 derivation 263.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A recursive collar and an ordinary cap construct one
actual supported finite PL deformation with all cap levels,
the fixed residual and the complete birth-interval decomposition.
See Alexander p. 7 and M76 derivation 263. -/
theorem AlexanderCollarSlab.exists_ordinary_capped_deformation
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hqP : q ∉ P.boundary ℝ) {d s₀ s₁ U : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ (P.boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ (P.boundary ℝ))
    (hunion : s₀ ∪ s₁ = S) (hinter : s₀ ∩ s₁ = P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) (hU : IsOpen U) (hdU : d ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q} ∧
      P.boundary ℝ \ {q} ⊆ closure ((s ∪ d) ∩ {x | 0 < A x}) ∧
      ∃ t : ℝ, t ∈ Ioo 0 β ∧ ∃ p : E, p ∈ d \ P.boundary ℝ ∧
        ∃ H : E ≃ₜ E,
          (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H : E → E) L.space) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' P.boundary ℝ) ∧
          (∀ x ∈ M.residual, H x = x) ∧
          (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H x = x) ∧
          (∀ x, β ≤ A x → H x = x) ∧
          (∀ x, x ∉ U → H x = x) ∧ (∀ x, δ ≤ |A x| → H x = x) ∧
          (∀ x, A x ≤ A (H x)) ∧
          (H '' (s ∪ d)) ∩ {x | A x = 0} = (((s ∪ d) ∩ {x | A x = 0}) \ d) ∧
          (H '' d) ∩ {x | A x = t * (2 / 3)} = {H p} ∧
          (∀ c : ℝ, c < t * (2 / 3) ∨ t < c → (H '' d) ∩ {x | A x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | A x ≤ t * a})
              ((H '' d) ∩ {x | A x = t * a})) ∧
          (∀ c : ℝ, c < 0 ∨ t ≤ c →
            ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
              ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
          ∀ c ∈ Ioo (0 : ℝ) t,
            ∃ (Z : Set E) (f : E → E) (X Y : Set E),
              FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ P.boundary ℝ ⊆ Z ∧
              s ∩ {x | A x = c} = (f '' P.boundary ℝ) ∪ X ∧
              Disjoint (f '' P.boundary ℝ) X ∧
              (H '' (s ∪ d)) ∩ {x | A x = c} = ((H '' d) ∩ {x | A x = c}) ∪ Y ∧
              Disjoint ((H '' d) ∩ {x | A x = c}) Y ∧
              ∃ F : X ≃ₜ Y, F.IsFinitePL := by
  have hP : P.boundary ℝ ⊆ S ∩ {x | A x = 0} :=
    subset_union_left.trans hsection.symm.subset
  have hqd : q ∉ d := fun h => hqP (hcap.subset ⟨h, M.apex_mem⟩)
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hcapT : d ∩ M.collar = P.boundary ℝ := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ hTS).trans hcap.subset
    · exact fun _ hx => ⟨hd.1 hx, M.bottom_covered (hP hx)⟩
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hselected, hside, happroach⟩ :=
    M.exists_selected_cut_side P hPe hPi hd hs₀ hs₁ hunion hinter hdplane hcap
      N hN hsection hdN
  have hsS : s ⊆ S := subset_union_left.trans hss.subset
  have hdmeet : d ∩ s ⊆ P.boundary ℝ :=
    (inter_subset_inter_right _ hsS).trans hcap.subset
  have hzeros : (s ∩ {x | A x = 0}) \ P.boundary ℝ ⊆ N.space := by
    rintro x ⟨hx, hxnb⟩
    exact (hsection.subset ⟨hsS hx.1, hx.2⟩).resolve_left hxnb
  obtain ⟨ec⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
  have hbconn := isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) ec q
  obtain ⟨x, hx⟩ := hbconn.nonempty
  obtain ⟨v, hv⟩ := M.exists_unit_height_direction (hP hx.1) hx.2
  let V := U ∩ {x | |A x| < δ}
  have hV : IsOpen V :=
    hU.inter (isOpen_lt A.continuous_of_finiteDimensional.abs continuous_const)
  have hdV : d ⊆ V := by
    intro x hx
    refine ⟨hdU hx, ?_⟩
    change |A x| < δ
    rwa [hdplane hx, abs_zero]
  obtain ⟨_, _, p, _, hp, _, _, _, _, _, ε, hε, H, hglobal, _, _, _, hall⟩ :=
    M.chart_finitePL.exists_protected_ordinary_capped_isotopy
      (fun x hx => (M.upper_bounds x hx).1) A M.width_pos M.cover M.height M.bottom
      hd hdplane q hqd M.apex_upper M.upper_pos hcapT hs hs'.isCompact.isClosed
      hsS hdmeet (hTS.trans hss.symm.subset) hssinter.subset hbconn hselected v hv
      N hN hsection hdN hzeros M.residualComplex M.residual_finite M.residual_space
      M.residual_zero M.roof_contact hV hdV
  obtain ⟨η, hη, hηroof⟩ := P.isCompact_boundary.exists_forall_le'
    (M.upper_finitePL.continuousOn.mono hP)
    (fun x hx => M.upper_pos x (hP hx) (fun hxq => hqP (hxq ▸ hx)))
  let τ := min ε (min η β) / 2
  have hsmall : 0 < min ε (min η β) := lt_min hε (lt_min hη M.width_pos)
  have hτ : 0 < τ := half_pos hsmall
  have hτsmall : τ < min ε (min η β) := half_lt_self hsmall
  have hτε : τ < ε := hτsmall.trans_le (min_le_left _ _)
  have hτη : τ < η := hτsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτβ : τ < β := hτsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let t : Icc (-ε) ε := ⟨τ, (neg_lt_zero.mpr hε).le.trans hτ.le, hτε.le⟩
  obtain ⟨hres, hnegative, hfix, hhigh, hball, hpositive⟩ := hall t
  obtain ⟨hraise, hzeroLevel, hminimum, hempty, hdisks, hterminal, hlow⟩ := hpositive hτ
  have hcomparisons := hs.exists_ordinary_terminal_level_comparisons A hdplane hτ (H t)
    hraise hnegative hhigh (fun c hc htc => by
      obtain ⟨F, hF, _⟩ := hterminal c hc htc
      exact ⟨F, hF⟩)
  refine ⟨s, s', hlabels, hside, happroach, τ, ⟨hτ, hτβ⟩, p, hp,
    H t, hglobal t, hball, hres, hnegative, hhigh, ?_, ?_, hraise,
    hzeroLevel, hminimum, hempty, hdisks, hcomparisons, ?_⟩
  · exact fun x hx => hfix x (fun h => hx h.1)
  · exact fun x hx => hfix x (fun h => (not_lt_of_ge hx) h.2)
  · intro c hc
    obtain ⟨f, X, Y, hf, hinj, hb, hsrc, hsep, htgt, hcapSep, F, hF, _⟩ :=
      hlow c ⟨hc.1, hc.2.trans hτβ⟩ hc.2
        (fun x hx => hc.2.trans (hτη.trans_le (hηroof x hx)))
    exact ⟨_, f, X, Y, hf, hinj, hb, hsrc, hsep, htgt, hcapSep, F, hF⟩

end Geometry
