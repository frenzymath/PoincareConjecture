import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalProperDiskCollarSide

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_centered_opposite_collar
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ I)) (hci : InjOn c (N.space ×ˢ I))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (positive : Bool) :
    ∃ C : E × ℝ → X, PolyhedralPLInCharts e C (N.space ×ˢ I) ∧
      InjOn C (N.space ×ˢ I) ∧
      C '' (N.space ×ˢ J) = c '' (N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε)) ∧
      C '' (N.space ×ˢ ({1 / 2} : Set ℝ)) = c '' (N.space ×ˢ ({0} : Set ℝ)) ∧
      C '' (N.space ×ˢ ({-(1 / 2)} : Set ℝ)) =
        c '' (N.space ×ˢ {if positive then -ε else ε}) := by
  let δ : ℝ := if positive then ε else -ε
  let T : ℝ →ᴬ[ℝ] ℝ := δ • (ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ (1/2))
  have hTval (t : ℝ) : T t = δ * (t - 1/2) := rfl
  have hδ : δ ≠ 0 := by cases positive <;> dsimp [δ] <;> linarith
  have hid : FinitePiecewiseAffineOn (id : E → E) N.space :=
    ⟨N,hN,rfl,N.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLI,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hT : FinitePiecewiseAffineOn T I := ⟨L,hL,hLI,L.affineOnFaces_affine T⟩
  let G := Prod.map (id : E → E) T
  have hG : FinitePiecewiseAffineOn G (N.space ×ˢ I) := hid.prodMap hT
  have hTin (t : ℝ) (ht : t ∈ I) : T t ∈ I := by
    rw [hTval]
    cases positive <;> dsimp [δ] <;> constructor <;> nlinarith [ht.1,ht.2]
  have hGmap : MapsTo G (N.space ×ˢ I) (N.space ×ˢ I) := fun z hz => ⟨hz.1,hTin _ hz.2⟩
  let C := c ∘ G
  have hC : PolyhedralPLInCharts e C (N.space ×ˢ I) := by
    obtain ⟨M,hM,hMs,hfaces⟩ := hG
    rw [←hMs]
    exact hc.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hfaces⟩
      (fun z hz => hGmap (hMs.subset hz))
  have hCi : InjOn C (N.space ×ˢ I) := by
    intro z hz w hw heq
    have hh := hci (hGmap hz) (hGmap hw) heq
    have hh1 := congrArg Prod.fst hh
    change z.1 = w.1 at hh1
    apply Prod.ext hh1
    have hh' : T z.2 = T w.2 := congrArg Prod.snd hh
    rw [hTval,hTval] at hh'
    linarith [mul_left_cancel₀ hδ hh']
  have hTint (t : ℝ) (ht : t ∈ J) : T t ∈ if positive then Icc (-ε) 0 else Icc 0 ε := by
    rw [hTval]
    cases positive <;> dsimp [δ] <;> constructor <;> nlinarith [ht.1,ht.2]
  have hGimage : G '' (N.space ×ˢ J) = N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨hz.1,hTint _ hz.2⟩
    · rintro ⟨x,u⟩ ⟨hx,hu⟩
      have hcase (v : ℝ) (hv : v ∈ J) (hTv : T v = u) :
          (x,u) ∈ G '' (N.space ×ˢ J) := ⟨(x,v),⟨hx,hv⟩,Prod.ext rfl hTv⟩
      cases positive
      · apply hcase (1/2-u/ε)
        · change u ∈ Icc 0 ε at hu
          have h0 := div_nonneg hu.1 hε.le
          have h1 : u / ε ≤ 1 := (div_le_iff₀ hε).mpr (by simpa using hu.2)
          constructor <;> linarith
        · rw [hTval]
          dsimp [δ]
          field_simp
          ring
      · apply hcase (u/ε+1/2)
        · change u ∈ Icc (-ε) 0 at hu
          have h0 : -1 ≤ u/ε := (le_div_iff₀ hε).mpr (by linarith [hu.1])
          have h1 := div_nonpos_of_nonpos_of_nonneg hu.2 hε.le
          constructor <;> linarith
        · rw [hTval]
          dsimp [δ]
          field_simp
          ring
  have hlevel (u : ℝ) : G '' (N.space ×ˢ {u}) = N.space ×ˢ {T u} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨hw.1,congrArg T hw.2⟩
    · rintro ⟨hz,ht⟩
      exact ⟨(z.1,u),⟨hz,rfl⟩,Prod.ext rfl ht.symm⟩
  refine ⟨C,hC,hCi,?_,?_,?_⟩
  · exact (image_comp c G _).trans (congrArg (image c) hGimage)
  · rw [show C = c ∘ G from rfl,image_comp,hlevel,hTval,sub_self,mul_zero]
  · rw [show C = c ∘ G from rfl,image_comp,hlevel,hTval]
    congr 3
    cases positive <;> dsimp [δ] <;> ring

end PoincareConjecture.M76
