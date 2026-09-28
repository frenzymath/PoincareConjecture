import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedOrientedCollars

set_option autoImplicit false
open Set Geometry PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_original_pair_oriented_polygon_collars
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (a : E ≃L[ℝ] P2) (e : ι → OpenPartialHomeomorph X F)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (A : Fin 2 → Set E) (c : ∀ j, squareAnnulus L d ≃ₜ A j)
    (hc : ∀ j, (c j).IsFinitePL) (f : Fin 2 → E → X) (τ : C3 → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f j (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) =
        τ (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j u, s)) :
    ∃ (B : ∀ j, OrientedPolygonCollar L d (A j)) (τ' : C3 → X),
      PolyhedralPLInCharts e τ' (identityTube L d) ∧
      τ' '' identityTube L d = τ '' identityTube L d ∧
      (∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        τ' z = τ' w ↔ z.1 = w.1 ∧
          (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∧
      (∃ r₀ r₁ : Bool, τ' = τ ∘ pairedTubeReindex r₀ r₁) ∧
      (∀ j p, depth L ((c j).symm ((B j).chart p)) = 0 ↔ depth L p = 0) ∧
      ∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        f j ((B j).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          annulus_period_point_mem hd hwidth _ u⟩) =
          τ' (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j u, s) := by
  classical
  choose m n P I rev hP hPi hI hIi hn hreg r b hr hb hbi hbval hrdepth hout hin hperiod
    using fun j ↦ exists_oriented_polygon_collar a hd hwidth (c j) (hc j)
  let b' (j : Fin 2) := (b j).trans (Homeomorph.setCongr (hreg j).symm)
  have hb' (j : Fin 2) : (b' j).IsFinitePL := by
    obtain ⟨g, hg, hbg⟩ := hb j
    exact ⟨g, hg, hbg⟩
  let B (j : Fin 2) : OrientedPolygonCollar L d (A j) :=
    ⟨m j, n j, P j, I j, hP j, hPi j, hI j, hIi j, hn j, hreg j,
      b' j, hb' j, hout j, hin j⟩
  let τ' := τ ∘ pairedTubeReindex (rev 0) (rev 1)
  obtain ⟨hPL, him, hfib'⟩ := pairedTubeReindex_map e (by linarith) hd
    (rev 0) (rev 1) τ hτ hfib
  refine ⟨B, τ', hPL, him, hfib', ⟨rev 0,rev 1,rfl⟩, ?_, ?_⟩
  · intro j p
    have hcp : (B j).chart p = c j (r j p) := Subtype.ext (hbval j p)
    rw [hcp, (c j).symm_apply_apply, hrdepth]
    cases rev j <;> simp
  intro j s hs u
  let v : Icc (-d) d := ⟨if rev j then -(u : ℝ) else u, by
    split_ifs <;> constructor <;> linarith [u.property.1, u.property.2]⟩
  have heq : r j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
      annulus_period_point_mem hd hwidth _ u⟩ =
      ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), v),
        annulus_period_point_mem hd hwidth _ v⟩ := Subtype.ext (hperiod j s hs u)
  change f j (b j _) = _
  rw [hbval, heq, hvalue j s hs v]
  apply congrArg τ
  apply Prod.ext
  · change PoincareConjecture.M76.Dehn.sourceTubeDiagonal j v =
      pairedArmReindex (rev 0) (rev 1) (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j u)
    rw [pairedArmReindex_diagonal]
    fin_cases j <;> rfl
  · rfl

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
