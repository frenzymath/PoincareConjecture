import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderGluing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.SquareAnnulusCylinder



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : Fin 2 → ℝ) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)

theorem exists_selected_annulus_cylinder :
    ∃ C : squareAnnulus 8 1 ≃ₜ Cyl, C.IsFinitePL ∧
      ∀ p, (C p : (Fin 2 → ℝ) × ℝ).2 = depth 8 p := by
  obtain ⟨_, H, _, _, hH, _, _⟩ :=
    ProtectedAnnulus.exists_source_square_annulus_coordinates
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hH
  let scale : P2 →ᴬ[ℝ] P2 := (1 / 8 : ℝ) • ContinuousAffineMap.id ℝ P2
  have hscaleval (p : P2) : scale p = (p.1 / 8, p.2 / 8) := by
    change ((1 / 8 : ℝ) * p.1, (1 / 8 : ℝ) * p.2) = _
    congr 1 <;> ring
  have hdepth (p : P2) : depth 1 (scale p) = depth 8 p / 8 := by
    rw [hscaleval]
    unfold depth
    change min (min (p.1 / 8) (p.2 / 8)) (min (1 - p.1 / 8) (1 - p.2 / 8)) = _
    rw [show (1 : ℝ) - p.1 / 8 = (8 - p.1) / 8 by ring,
      show (1 : ℝ) - p.2 / 8 = (8 - p.2) / 8 by ring]
    rw [min_div_div_right (by norm_num : (0 : ℝ) ≤ 8),
      min_div_div_right (by norm_num : (0 : ℝ) ≤ 8),
      min_div_div_right (by norm_num : (0 : ℝ) ≤ 8)]
  have hf : FinitePiecewiseAffineOn scale (squareAnnulus 8 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine scale⟩
  have hi : InjOn scale (squareAnnulus 8 1) := by
    intro p _ q _ h
    rw [hscaleval, hscaleval] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (by dsimp at h1; linarith) (by dsimp at h2; linarith)
  have himage : scale '' squareAnnulus 8 1 = squareAnnulus 1 (1 / 8) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [mem_squareAnnulus_iff_depth, hdepth]
      have h := mem_squareAnnulus_iff_depth.mp hq
      constructor <;> linarith [h.1, h.2]
    · intro hp
      let q : P2 := (8 * p.1, 8 * p.2)
      have hq : scale q = p := by rw [hscaleval]; dsimp [q]; ext <;> dsimp <;> ring
      have hd := hdepth q
      rw [hq] at hd
      have h := mem_squareAnnulus_iff_depth.mp hp
      refine ⟨q, mem_squareAnnulus_iff_depth.mpr ⟨?_, ?_⟩, hq⟩ <;>
        linarith [h.1, h.2]
  obtain ⟨S, hS, hSv⟩ := hf.exists_homeomorph_image hi
  let T := S.trans (Homeomorph.setCongr himage)
  obtain ⟨C, hC, hCv⟩ := exists_finitePL_square_annulus_cylinder
  refine ⟨T.trans C, (hS.setCongr rfl himage).trans hC, ?_⟩
  intro p
  change (C (T p) : (Fin 2 → ℝ) × ℝ).2 = _
  rw [hCv]
  have hTv : (T p : P2) = scale p := hSv p
  rw [hTv, hdepth]
  ring

end PoincareConjecture.M76.Dehn.Annuli
