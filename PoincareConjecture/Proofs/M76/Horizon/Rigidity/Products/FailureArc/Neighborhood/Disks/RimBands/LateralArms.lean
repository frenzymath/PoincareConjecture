import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.CornerMatching







set_option autoImplicit false
noncomputable section
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def armCoordinates (δ t₀ t₁ : ℝ) (b : Bool) : P2 →ᴬ[ℝ] P2 :=
  ((δ * sign b) • (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
    (ContinuousAffineMap.const ℝ P2 t₀ +
      (t₁-t₀) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)

theorem armCoordinates_apply (δ t₀ t₁ : ℝ) (b : Bool) (p : P2) :
    armCoordinates δ t₀ t₁ b p = (δ * (sign b * p.1),(1-p.2)*t₀+p.2*t₁) := by
  change (δ * sign b * p.1,t₀+(t₁-t₀)*p.2) = _
  apply Prod.ext <;> dsimp <;> ring

theorem armCoordinates_bijOn {δ t₀ t₁ : ℝ} (hδ : 0 < δ)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (b : Bool) :
    BijOn (armCoordinates δ t₀ t₁ b) (parameter 1) (parameter δ) := by
  have hin (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1-t)*t₀+t*t₁ ∈ Icc (0 : ℝ) 1 := by
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp only [mul_zero,mul_one,zero_add,add_zero]
    · exact ht
    · exact ⟨by linarith [ht.2],by linarith [ht.1]⟩
  refine ⟨?_,?_,?_⟩
  · intro p hp
    rw [armCoordinates_apply]
    refine ⟨?_,hin p.2 hp.2⟩
    have hs : sign b * p.1 ∈ Icc (-1 : ℝ) 1 := by
      cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
      · exact hp.1
      · exact ⟨by linarith [hp.1.2],by linarith [hp.1.1]⟩
    exact ⟨by nlinarith [hs.1],by nlinarith [hs.2]⟩
  · intro p hp q hq heq
    rw [armCoordinates_apply,armCoordinates_apply] at heq
    have h0 := congrArg Prod.fst heq
    have h1 := congrArg Prod.snd heq
    apply Prod.ext
    · have hsg : sign b * p.1 = sign b * q.1 := mul_left_cancel₀ hδ.ne' h0
      have hsg' := congrArg (fun s => sign b * s) hsg
      simpa only [sign_mul_sign] using hsg'
    · rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> dsimp at h1 <;> nlinarith
  · intro p hp
    have hx : sign b * p.1 / δ ∈ Icc (-1 : ℝ) 1 := by
      have hs : sign b * p.1 ∈ Icc (-δ) δ := by
        cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
        · exact hp.1
        · exact ⟨by linarith [hp.1.2],by linarith [hp.1.1]⟩
      exact ⟨(le_div_iff₀ hδ).mpr (by linarith [hs.1]),
        (div_le_iff₀ hδ).mpr (by linarith [hs.2])⟩
    have hxval : δ * (sign b * (sign b * p.1 / δ)) = p.1 := by
      rw [← mul_div_assoc,sign_mul_sign,mul_div_cancel₀ _ hδ.ne']
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · refine ⟨(sign b * p.1 / δ,p.2),⟨hx,hp.2⟩,?_⟩
      rw [armCoordinates_apply]
      simp only [mul_zero,mul_one,zero_add,hxval]
    · refine ⟨(sign b * p.1 / δ,1-p.2),⟨hx,by
        exact ⟨by linarith [hp.2.2],by linarith [hp.2.1]⟩⟩,?_⟩
      rw [armCoordinates_apply,hxval]
      apply Prod.ext
      · rfl
      · dsimp; ring

theorem armCoordinates_finitePL (δ t₀ t₁ : ℝ) (b : Bool) :
    FinitePiecewiseAffineOn (armCoordinates δ t₀ t₁ b) (parameter 1) := by
  have h := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := h
  exact ⟨K,hK,hKs,K.affineOnFaces_affine (armCoordinates δ t₀ t₁ b)⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

def prescribedArmBand (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r δ t₀ t₁ : ℝ) (j b : Bool) : P2 → X :=
  originalBandMap U r (b,if j then !b else b) ∘ armCoordinates δ t₀ t₁ b

theorem prescribedArmBand_properties
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) {r δ t₀ t₁ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (j b : Bool) :
    PolyhedralPLInCharts e (prescribedArmBand U r δ t₀ t₁ j b) (parameter 1) ∧
      IsEmbedding (fun p : parameter 1 => prescribedArmBand U r δ t₀ t₁ j b p) ∧
      MapsTo (prescribedArmBand U r δ t₀ t₁ j b) (parameter 1)
        (frontier (R \ U.map '' openTube r)) ∧
      prescribedArmBand U r δ t₀ t₁ j b '' parameter 1 =
        U.map '' band r δ (b,if j then !b else b) ∧
      (∀ t : ℝ, prescribedArmBand U r δ t₀ t₁ j b (0,t) =
        originalBandMap U r (b,if j then !b else b) (0,(1-t)*t₀+t*t₁)) ∧
      (∀ p ∈ parameter 1, prescribedArmBand U r δ t₀ t₁ j b p ∈ frontier R ↔
        p.2=0 ∨ p.2=1) := by
  have hbij := armCoordinates_bijOn hδ horder b
  obtain ⟨hB,hBi,hBQ,_,_,hBp,hBimage⟩ :=
    originalBandMap_properties U hR he hδ hδr hr1 (b,if j then !b else b)
  have hA := armCoordinates_finitePL δ t₀ t₁ b
  have hA' := hA
  obtain ⟨K,hK,hKs,_⟩ := hA'
  have hPL : PolyhedralPLInCharts e (prescribedArmBand U r δ t₀ t₁ j b)
      (parameter 1) := hKs ▸ hB.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hA)
        (fun p hp => hbij.1 (hKs.subset hp))
  let : CompactSpace (parameter 1) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  refine ⟨hPL,?_,hBQ.comp hbij.1,?_,?_,?_⟩
  · apply (hPL.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro p q hpq
    have hab := congrArg Subtype.val (hBi.injective
      (a₁ := ⟨_,hbij.1 p.property⟩) (a₂ := ⟨_,hbij.1 q.property⟩) hpq)
    exact Subtype.ext (hbij.2.1 p.property q.property hab)
  · change (_ ∘ _) '' _ = _
    rw [Set.image_comp,hbij.image_eq,hBimage]
  · intro t
    simp only [prescribedArmBand,Function.comp_apply,armCoordinates_apply,mul_zero]
  · intro p hp
    change originalBandMap U r (b,if j then !b else b) (armCoordinates δ t₀ t₁ b p) ∈
      frontier R ↔ _
    rw [hBp _ (hbij.1 hp),armCoordinates_apply]
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp
    · simp only [mul_zero,mul_one,add_zero]
      constructor <;> rintro (h|h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
