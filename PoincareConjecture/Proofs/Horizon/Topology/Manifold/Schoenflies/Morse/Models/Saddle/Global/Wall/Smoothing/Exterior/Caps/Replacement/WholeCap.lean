import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.RelativeRadial
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Levels
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.HeightCorrection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1

theorem exists_relative_canonical_cap_replacement_of_cylindrical_coordinates
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hGheight : ∀ p, G p 2 = p 2)
    {σ : Real} (hσ : 0 < σ)
    (hG : ∀ t, |t| ≤ σ → ∀ q : E2,
      G (tangentPlanarLatitude t q) = sliceAtHeight t (A q)) :
    ∃ (η : Real) (E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ (∀ p : E3, p 2 ≤ η → E p = p) ∧
      E '' (planarCapLift A '' boundedCylinderNorthernCap axis) =
        G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}) := by
  obtain ⟨τ, hτ, _, hτhalf, H, r, hHm, hH0, hr, hrpos, hHr, hHlocal, hrlocal, _⟩ :=
    Replacement.exists_cylindrical_height_and_radius (by norm_num : (0 : Real) < 1 / 4)
  let κ := min τ σ / 2
  have hκ : 0 < κ := half_pos (lt_min hτ hσ)
  have hκτ : κ ≤ τ := by
    have := min_le_left τ σ
    dsimp [κ]
    linarith [lt_min hτ hσ]
  have hκσ : κ ≤ σ := by
    have := min_le_right τ σ
    dsimp [κ]
    linarith [lt_min hτ hσ]
  have hκhalf : κ < 1 / 2 := hκτ.trans_lt hτhalf
  have hheight : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p : S2 => (p : E3) 2) :=
    (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contMDiff.comp contMDiff_coe_sphere
  have hrS : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p : S2 => r ((p : E3) 2)) :=
    hr.contMDiff.comp hheight
  have hrmatch (p : S2) (hp : (p : E3) 2 ∈ Icc (0 : Real) κ) :
      boundedCylinderRadius axis p = r ((p : E3) 2) := by
    have hi : inner Real axis (p : E3) = (p : E3) 2 := by
      simp [axis, EuclideanSpace.inner_single_left]
    rw [boundedCylinderRadius_of_abs_height_le axis p (by
      rw [hi, abs_of_nonneg hp.1]; exact hp.2.trans hκhalf.le), hi,
        hrlocal _ (by rw [abs_of_nonneg hp.1]; exact hp.2.trans hκτ)]
  obtain ⟨ηq, Q, hηq, hQfix, _, hQ⟩ := exists_relative_radial_upper_cap_transport
    (boundedCylinderRadius axis) (fun p : S2 => r ((p : E3) 2))
    (contMDiff_boundedCylinderRadius axis) hrS (boundedCylinderRadius_pos axis)
    (fun p => hrpos _) hκ hrmatch
  let B := horizontalScaleLift r hr hrpos
  let S := sphere (0 : E3) 1 ∩ {p : E3 | 0 ≤ p 2}
  have hZH (p : E3) : verticalCapLift H (B p) = r (p 2) • p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hHr _
  have hQcap : Q '' boundedCylinderNorthernCap axis = verticalCapLift H '' (B '' S) := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have hp0 : 0 ≤ (p : E3) 2 := by simpa [axis, EuclideanSpace.inner_single_left] using hp
      exact ⟨B p, ⟨p, ⟨p.property, hp0⟩, rfl⟩, (hZH p).trans (hQ p hp0).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨boundedCylinderRadius axis ⟨p, hp.1⟩ • p,
        ⟨⟨p, hp.1⟩, by simpa [axis, EuclideanSpace.inner_single_left] using hp.2, rfl⟩, ?_⟩
      exact (hQ ⟨p, hp.1⟩ hp.2).trans (hZH p).symm
  let β := κ / 2
  have hβ : 0 < β := half_pos hκ
  have hβκ : β ≤ κ := (half_lt_self hκ).le
  have hHβ : 0 < H β := by simpa only [hH0] using hHm hβ
  obtain ⟨ε, hε, _, _, K, hKm, hKfix, hKoutside⟩ :=
    Replacement.exists_lower_fixed_cylindrical_height_correction H hτ hHβ hHlocal
  let L := H.trans K
  have hLm : StrictMono L := hKm.comp hHm
  have hL0 : L 0 = 0 := by change K (H 0) = 0; rw [hH0, hKfix 0 hε.le]
  have hLfix (t : Real) (ht : β ≤ t) : L t = t := by
    change K (H t) = t
    rw [hKoutside _ (hHm.monotone ht), H.symm_apply_apply]
  have hpres : verticalCapLift L '' (B '' S) = B '' S :=
    verticalCapLift_preserves_upper_scale_cap r hr hrpos hβ
      (by linarith : β < 1)
      (fun t ht => hrlocal t (by rw [abs_of_nonneg ht.1]; exact ht.2.trans (hβκ.trans hκτ)))
      L hLm hL0 hLfix
  have hKcap : verticalCapLift K '' (verticalCapLift H '' (B '' S)) = B '' S := by
    rw [image_image]
    have he : (verticalCapLift K ∘ verticalCapLift H) = verticalCapLift L := by
      funext p
      ext i
      fin_cases i <;> rfl
    change (verticalCapLift K ∘ verticalCapLift H) '' (B '' S) = B '' S
    rw [he, hpres]
  have hKlow (p : E3) (hp : p 2 ≤ ε) : verticalCapLift K p = p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hKfix _ hp
  let LA := planarCapLift A
  let T := ((LA.symm.trans Q).trans (verticalCapLift K)).trans LA
  have hLAi (p : E3) : LA.symm p 2 = p 2 := by
    have he := planarCapLift_height A (LA.symm p)
    change LA (LA.symm p) 2 = _ at he
    rw [LA.apply_symm_apply] at he
    exact he.symm
  have hTfix (p : E3) (hp : p 2 ≤ min ηq ε) : T p = p := by
    change LA (verticalCapLift K (Q (LA.symm p))) = p
    rw [hQfix _ (by rw [hLAi]; exact hp.trans (min_le_left _ _)),
      hKlow _ (by rw [hLAi]; exact hp.trans (min_le_right _ _)), LA.apply_symm_apply]
  have hTcap : T '' (LA '' boundedCylinderNorthernCap axis) = LA '' (B '' S) := by
    have he : T '' (LA '' boundedCylinderNorthernCap axis) =
        LA '' (verticalCapLift K '' (Q '' boundedCylinderNorthernCap axis)) := by
      rw [image_image, image_image, image_image]
      apply image_congr
      intro p _
      change LA (verticalCapLift K (Q (LA.symm (LA p)))) = _
      rw [LA.symm_apply_apply]
    rw [he, hQcap, hKcap]
  obtain ⟨ηg, E, hηg, hEfix, _, hEcap⟩ := exists_relative_cylindrical_cap_graft A G hGheight hκ
    (by linarith : κ < 1) (fun t ht q => hG t (ht.trans hκσ) q) r hr hrpos
    (fun t ht => hrlocal t (ht.trans hκτ))
  refine ⟨min (min ηq ε) ηg, T.trans E, lt_min (lt_min hηq hε) hηg, ?_, ?_⟩
  · intro p hp
    change E (T p) = p
    rw [hTfix p (hp.trans (min_le_left _ _)), hEfix p (hp.trans (min_le_right _ _))]
  · change (E ∘ T) '' (LA '' boundedCylinderNorthernCap axis) = G '' S
    rw [image_comp, hTcap]
    exact hEcap

theorem exists_relative_profile_cap_replacement {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real) :
    ∃ (η : Real) (G E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ (∀ p : E3, p 2 ≤ η → E p = p) ∧
      (∀ p, G p 2 = p 2) ∧
      (∀ t, |t| ≤ 1 / 16 → ∀ q : E2, G (tangentPlanarLatitude t q) =
        sliceAtHeight t (profilePlanarDiffeomorph hρ H a R 0
          (by constructor <;> norm_num) q)) ∧
      E '' (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
        (by constructor <;> norm_num)) '' boundedCylinderNorthernCap axis) =
          G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}) := by
  obtain ⟨G, hGh, hG, _, _⟩ := exists_profile_cap_with_canonical_collar hρ H a R
  obtain ⟨η, E, hη, hE, hcap⟩ :=
    exists_relative_canonical_cap_replacement_of_cylindrical_coordinates
      (profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num))
      G hGh (by norm_num : (0 : Real) < 1 / 16) hG
  exact ⟨η, G, E, hη, hE, hGh, hG, hcap⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
