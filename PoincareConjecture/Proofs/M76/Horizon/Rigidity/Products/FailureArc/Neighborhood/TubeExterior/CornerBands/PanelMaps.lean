import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Contacts



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def panelParameter (r δ : ℝ) : Set P2 := Icc (-r + δ) (r - δ) ×ˢ Icc 0 1

noncomputable def panelAffine (r : ℝ) (i : Bool × Bool) : P2 →ᴬ[ℝ] C3 :=
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let b := ContinuousAffineMap.const ℝ P2 (sign i.2 * r)
  (if i.1 then a.prod b else b.prod a).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

theorem panelAffine_injective (r : ℝ) (i : Bool × Bool) : Function.Injective (panelAffine r i) := by
  intro p q h
  apply Prod.ext
  · rcases i with ⟨axis,s⟩
    cases axis
    · exact congrArg (fun z : C3 => z.1.2) h
    · exact congrArg (fun z : C3 => z.1.1) h
  · exact congrArg (fun z : C3 => z.2) h

theorem panelAffine_image (r δ : ℝ) (i : Bool × Bool) :
    panelAffine r i '' panelParameter r δ = panel r δ i := by
  rcases i with ⟨axis,s⟩
  cases axis <;> ext z
  · constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨rfl,hp.1⟩,hp.2⟩
    · rintro ⟨⟨hx,hy⟩,ht⟩
      exact ⟨(z.1.2,z.2),⟨hy,ht⟩,Prod.ext (Prod.ext hx.symm rfl) rfl⟩
  · constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨hp.1,rfl⟩,hp.2⟩
    · rintro ⟨⟨hx,hy⟩,ht⟩
      exact ⟨(z.1.1,z.2),⟨hx,ht⟩,Prod.ext (Prod.ext rfl hy.symm) rfl⟩

theorem panelAffine_finitePL {r δ : ℝ} (hδr : δ < r) (i : Bool × Bool) :
    FinitePiecewiseAffineOn (panelAffine r i) (panelParameter r δ) := by
  have hball := (isFinitePLBallPair_Icc (show -r + δ < r - δ by linarith)).prod
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  exact ⟨K,hK,hKs,K.affineOnFaces_affine (panelAffine r i)⟩

theorem panel_subset_lateral {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) (i : Bool × Bool) :
    panel r δ i ⊆ lateral r := fun _ hz =>
  ((lateral_sdiff_openBands hδ hδr).symm.subset (mem_iUnion.mpr ⟨i,hz⟩)).1

theorem panel_avoids_diagonals {r δ : ℝ} (hδ : 0 < δ)
    {i : Bool × Bool} {z : C3} (hz : z ∈ panel r δ i) :
    z.1.2 ≠ z.1.1 ∧ z.1.2 ≠ -z.1.1 := by
  have hh := hz.1
  rcases i with ⟨axis,s⟩
  cases axis <;> cases s <;>
    simp only [edgeFootprint,sign,Bool.false_eq_true,if_false,if_true,
      one_mul,neg_one_mul,mem_prod,mem_singleton_iff,mem_Icc] at hh
  all_goals constructor <;> intro h <;> linarith [hh.1,hh.2]

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

noncomputable def originalPanelMap
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (r : ℝ) (i : Bool × Bool) : P2 → X :=
  U.map ∘ panelAffine r i

theorem originalPanelMap_properties
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1) (i : Bool × Bool) :
    PolyhedralPLInCharts e (originalPanelMap U r i) (panelParameter r δ) ∧
      IsEmbedding (fun p : panelParameter r δ => originalPanelMap U r i p) ∧
      MapsTo (originalPanelMap U r i) (panelParameter r δ) (frontier (R \ U.map '' openTube r)) ∧
      (∀ p ∈ panelParameter r δ, originalPanelMap U r i p ∉ f₀ '' S ∧
        originalPanelMap U r i p ∉ f₁ '' T) ∧
      (∀ p ∈ panelParameter r δ, originalPanelMap U r i p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
      originalPanelMap U r i '' panelParameter r δ = U.map '' panel r δ i := by
  have hpanel : MapsTo (panelAffine r i) (panelParameter r δ) (panel r δ i) :=
    fun p hp => (panelAffine_image r δ i).subset (mem_image_of_mem _ hp)
  have hmap : MapsTo (panelAffine r i) (panelParameter r δ) tube := fun p hp =>
    closedTube_subset hr1 (lateral_subset r (panel_subset_lateral hδ hδr i (hpanel hp)))
  have hPL : PolyhedralPLInCharts e (originalPanelMap U r i) (panelParameter r δ) := by
    have hf := panelAffine_finitePL hδr i
    have hf' := hf
    obtain ⟨K,hK,hKs,_⟩ := hf'
    have h := U.pl.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hf)
      (fun p hp => hmap (hKs.subset hp))
    exact hKs ▸ h
  let : CompactSpace (panelParameter r δ) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have hinj : InjOn (originalPanelMap U r i) (panelParameter r δ) := by
    intro p hp q hq hpq
    apply panelAffine_injective r i
    exact congrArg Subtype.val (U.embedding.injective
      (a₁ := ⟨_,hmap hp⟩) (a₂ := ⟨_,hmap hq⟩) hpq)
  refine ⟨hPL,?_,?_,?_,?_,?_⟩
  · exact (hPL.continuousOn.domRestrict.isClosedEmbedding
      (fun p q h => Subtype.ext (hinj p.property q.property h))).isEmbedding
  · intro p hp
    rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he (hδ.trans hδr) hr1]
    exact Or.inr ⟨_,panel_subset_lateral hδ hδr i (hpanel hp),rfl⟩
  · intro p hp
    have h := panel_avoids_diagonals hδ (hpanel hp)
    exact ⟨fun hx => h.1 ((U.first_trace _ (hmap hp)).mp hx),
      fun hx => h.2 ((U.second_trace _ (hmap hp)).mp hx)⟩
  · intro p hp
    exact U.frontier_iff _ (hmap hp)
  · change (U.map ∘ panelAffine r i) '' _ = _
    rw [← panelAffine_image r δ i,image_image]
    rfl

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
