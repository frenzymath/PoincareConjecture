import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.HalfPatch
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.PlanarSides

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "J" => Icc (0 : ℝ) 1

def stripReflection (b : Bool) : P2 →ᴬ[ℝ] P2 :=
  (sign b • (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

@[simp] theorem stripReflection_apply (b : Bool) (p : P2) :
    stripReflection b p = (sign b*p.1,p.2) := rfl

theorem stripReflection_involutive (b : Bool) : Function.Involutive (stripReflection b) := by
  intro p
  cases b <;> simp [sign]

theorem stripReflection_mem (b : Bool) {w : ℝ} {p : P2} :
    stripReflection b p ∈ parameter w ↔ p ∈ parameter w := by
  cases b
  · simp [parameter,sign]
  · simp only [stripReflection_apply,parameter,mem_prod,mem_Icc,sign,if_true,neg_one_mul]
    constructor <;> rintro ⟨⟨h0,h1⟩,ht⟩ <;> exact ⟨⟨by linarith,by linarith⟩,ht⟩

theorem finitePL_stripReflection_comp {w : ℝ} {g : P2 → P2}
    (hg : FinitePiecewiseAffineOn g (parameter w)) (b : Bool) :
    FinitePiecewiseAffineOn (g ∘ stripReflection b) (parameter w) := by
  have hg' := hg
  obtain ⟨K,hK,hKs,_⟩ := hg'
  have hA : FinitePiecewiseAffineOn (stripReflection b) (parameter w) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (stripReflection b)⟩
  exact hg.comp hA (fun _ hp => (stripReflection_mem b).mpr hp)

theorem exists_oriented_strip_reparametrization {w : ℝ} (hw : 0 < w) {g : P2 → P2}
    (hg : FinitePiecewiseAffineOn g (parameter w)) (hi : InjOn g (parameter w))
    (hcenter : ∀ t ∈ J, g (0,t) = (t,0))
    (hzero : ∀ p ∈ parameter w, (g p).2=0 ↔ p.1=0) :
    ∃ b : Bool,
      FinitePiecewiseAffineOn (g ∘ stripReflection b) (parameter w) ∧
      InjOn (g ∘ stripReflection b) (parameter w) ∧
      (∀ t ∈ J, (g ∘ stripReflection b) (0,t) = (t,0)) ∧
      (∀ p ∈ parameter w, ((g ∘ stripReflection b) p).2=0 ↔ p.1=0) ∧
      (∀ p ∈ Ioc (0 : ℝ) w ×ˢ J, 0 < ((g ∘ stripReflection b) p).2) ∧
      (∀ p ∈ Ico (-w) 0 ×ˢ J, ((g ∘ stripReflection b) p).2 < 0) := by
  obtain ⟨b,hpos,hneg⟩ := exists_planar_strip_orientation hw hg hi hcenter hzero
  refine ⟨b,finitePL_stripReflection_comp hg b,?_,?_,?_,?_,?_⟩
  · intro p hp q hq heq
    exact (stripReflection_involutive b).injective
      (hi ((stripReflection_mem b).mpr hp) ((stripReflection_mem b).mpr hq) heq)
  · intro t ht
    simpa using hcenter t ht
  · intro p hp
    rw [Function.comp_apply,hzero _ ((stripReflection_mem b).mpr hp)]
    cases b <;> simp [sign]
  · intro p hp
    cases b
    · simpa [sign] using hpos p hp
    · have h := hneg (-p.1,p.2) ⟨⟨by linarith [hp.1.2],by linarith [hp.1.1]⟩,hp.2⟩
      simpa [sign] using h
  · intro p hp
    cases b
    · simpa [sign] using hneg p hp
    · have h := hpos (-p.1,p.2) ⟨⟨by linarith [hp.1.2],by linarith [hp.1.1]⟩,hp.2⟩
      simpa [sign] using h

def halfPatchInput (a : Bool) : P2 →ᴬ[ℝ] P2 :=
  (sign a • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

def halfPatchOutput (a : Bool) : P2 →ᴬ[ℝ] P2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    (sign a • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)

@[simp] theorem halfPatchInput_apply (a : Bool) (p : P2) :
    halfPatchInput a p = (sign a*p.2,p.1) := rfl

@[simp] theorem halfPatchOutput_apply (a : Bool) (p : P2) :
    halfPatchOutput a p = (p.1,sign a*p.2) := rfl

theorem exists_oriented_half_patches {w : ℝ} (hw : 0 < w) (hwsmall : w ≤ 1/2)
    {g : P2 → P2} (hg : FinitePiecewiseAffineOn g (parameter w))
    (hi : InjOn g (parameter w))
    (hmap : MapsTo g (parameter w)
      (Ioo (-(1/2 : ℝ)) (3/2) ×ˢ Ioo (-(1/2 : ℝ)) (1/2)))
    (hcenter : ∀ t ∈ J, g (0,t)=(t,0))
    (hzero : ∀ p ∈ parameter w, (g p).2=0 ↔ p.1=0)
    (hpos : ∀ p ∈ Ioc (0 : ℝ) w ×ˢ J, 0 < (g p).2)
    (hneg : ∀ p ∈ Ico (-w) 0 ×ˢ J, (g p).2 < 0) (a : Bool) :
    ∃ H : halfArmRectangle ≃ₜ halfArmRectangle, H.IsFinitePL ∧
      (∀ p : halfArmPatch (w/2), (H ⟨p,by
        exact ⟨⟨by linarith [p.property.1.1],by linarith [p.property.1.2]⟩,
          ⟨p.property.2.1,by linarith [p.property.2.2]⟩⟩⟩ : P2) =
          halfPatchOutput a (g (halfPatchInput a p))) ∧
      (∀ p : halfArmRectangle, (p : P2) ∈ frontier halfArmRectangle → H p=p) ∧
      (∀ p : halfArmRectangle, (p : P2) ∈ halfArmPatch (w/2) ↔
        (H p : P2) ∈ (halfPatchOutput a ∘ g ∘ halfPatchInput a) '' halfArmPatch (w/2)) := by
  have hinput : MapsTo (halfPatchInput a) (halfArmPatch (w/2)) (parameter w) := by
    intro p hp
    refine ⟨?_,hp.1⟩
    cases a <;> simp only [halfPatchInput_apply,sign,Bool.false_eq_true,if_false,if_true,
      one_mul,neg_one_mul,mem_Icc]
    all_goals constructor <;> linarith [hp.2.1,hp.2.2]
  have hball := (isFinitePLBallPair_Icc zero_lt_one).prod (isFinitePLBallPair_Icc (half_pos hw))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  have hA : FinitePiecewiseAffineOn (halfPatchInput a) (halfArmPatch (w/2)) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (halfPatchInput a)⟩
  have hfin := (hg.comp hA hinput).postcomp (halfPatchOutput a)
  have hiA : Function.Injective (halfPatchInput a) := by
    intro p q heq
    cases a <;> simpa [sign,Prod.ext_iff,and_comm] using heq
  have hiB : Function.Injective (halfPatchOutput a) := by
    intro p q heq
    cases a <;> simpa [sign,Prod.ext_iff] using heq
  apply exists_half_arm_patch_extension (half_pos hw) (by linarith) hfin
    (fun p hp q hq heq => hiA (hi (hinput hp) (hinput hq) (hiB heq)))
  · intro p hp
    have hm := hmap (hinput hp)
    refine ⟨hm.1,?_,?_⟩
    · by_cases hz : p.2=0
      · have hz' := (hzero _ (hinput hp)).mpr (by simp [hz])
        simp only [Function.comp_apply,halfPatchOutput_apply,hz',mul_zero,le_refl]
      · have hp' : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hz)
        cases a
        · have h := hpos (p.2,p.1) ⟨⟨hp',by linarith [hp.2.2]⟩,hp.1⟩
          simpa [sign] using h.le
        · have h := hneg (-p.2,p.1) ⟨⟨by linarith [hp.2.2],by linarith⟩,hp.1⟩
          simpa [sign] using (neg_nonneg.mpr h.le)
    · cases a
      · simpa [sign] using hm.2.2
      · simpa [sign] using (neg_lt_neg hm.2.1)
  · intro t ht
    simp only [Function.comp_apply,halfPatchInput_apply,mul_zero,hcenter t ht,halfPatchOutput_apply]
  · intro p hp
    have hz := hzero (halfPatchInput a p) (hinput hp)
    cases a <;> simpa [sign] using hz

end PoincareConjecture.M76.Dehn.Annuli.RimBands
