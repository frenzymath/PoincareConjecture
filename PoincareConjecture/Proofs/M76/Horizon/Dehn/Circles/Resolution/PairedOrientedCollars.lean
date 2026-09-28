import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OrientedCollar
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.TubeArmReindex









set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)



structure OrientedPolygonCollar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L d : ℝ) (A : Set E) where
  outerSize : ℕ
  innerSize : ℕ
  outer : Polygon E (outerSize + 3)
  inner : Polygon E (innerSize + 3)
  outer_simplicial : outer.HasSimplicialEdges
  outer_injective : Function.Injective outer
  inner_simplicial : inner.HasSimplicialEdges
  inner_injective : Function.Injective inner
  nested : closure inner.inside ⊆ outer.inside
  carrier : A = closure outer.inside \ inner.inside
  chart : squareAnnulus L d ≃ₜ A
  chart_PL : chart.IsFinitePL
  outer_depth : ∀ p, (chart p : E) ∈ outer.boundary ℝ ↔ depth L p = -d
  inner_depth : ∀ p, (chart p : E) ∈ inner.boundary ℝ ↔ depth L p = d



theorem exists_paired_oriented_polygon_collars
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (a : E ≃L[ℝ] P2) (e : ι → OpenPartialHomeomorph X F)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (A : Fin 2 → Set E) (c : ∀ j, squareAnnulus L d ≃ₜ A j)
    (hc : ∀ j, (c j).IsFinitePL) (f : E → X) (τ : C3 → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) =
        τ (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j u, s)) :
    ∃ (B : ∀ j, OrientedPolygonCollar L d (A j)) (τ' : C3 → X),
      PolyhedralPLInCharts e τ' (identityTube L d) ∧
      τ' '' identityTube L d = τ '' identityTube L d ∧
      (∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        τ' z = τ' w ↔ z.1 = w.1 ∧
          (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∧
      (∀ j p, depth L ((c j).symm ((B j).chart p)) = 0 ↔ depth L p = 0) ∧
      ∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        f ((B j).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
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
  refine ⟨B, τ', hPL, him, hfib', ?_, ?_⟩
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
  change f (b j _) = _
  rw [hbval, heq, hvalue j s hs v]
  apply congrArg τ
  apply Prod.ext
  · change PoincareConjecture.M76.Dehn.sourceTubeDiagonal j v =
      pairedArmReindex (rev 0) (rev 1) (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j u)
    rw [pairedArmReindex_diagonal]
    fin_cases j <;> rfl
  · rfl

end Dehn
