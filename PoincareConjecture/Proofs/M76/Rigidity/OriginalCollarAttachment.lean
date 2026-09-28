import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarCoreMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarShellBoundary
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCubeShellGluing
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCollarStrip

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {K : Set X}

theorem ChartwisePLBall.attach_collar (he : PLDomain e K)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier K) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (L.space ×ˢ I) K)
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    (hproper : ∀ z : (L.space ×ˢ I : Set (E × ℝ)),
      c z ∈ frontier K ↔ (z : E × ℝ).2 = 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (b : ChartwisePLBall e (K \ c '' (L.space ×ˢ Ico 0 ε))
      (c '' (L.space ×ˢ {ε}))) :
    Nonempty (ChartwisePLBall e K (frontier K)) := by
  let U := c '' (L.space ×ˢ Ico 0 ε)
  let N := c '' (L.space ×ˢ Icc 0 ε)
  let C := K \ U
  let S := c '' (L.space ×ˢ {ε})
  have hcInj : InjOn c (L.space ×ˢ I) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw)
  obtain ⟨_, hNK, hUN, _, hNdif, hFU⟩ := compact_collar_strip_geometry
    (L.isCompact_space_of_finite hL) HB c hc.continuousOn hcInj hinside hbase hε hε1
  have hcover : C ∪ N = K := by
    ext x
    constructor
    · exact fun hx => hx.elim (fun h => h.1) (fun h => hNK h)
    · intro hx
      by_cases hxU : x ∈ U
      · exact Or.inr (hUN hxU)
      · exact Or.inl ⟨hx, hxU⟩
  have hoverlap : C ∩ N = S := by
    calc
      C ∩ N = N \ U := by
        ext x
        constructor
        · exact fun hx => ⟨hx.2, hx.1.2⟩
        · exact fun hx => ⟨⟨hNK hx.1, hx.2⟩, hx.1⟩
      _ = S := hNdif
  have hCfront : Disjoint C (frontier K) :=
    Set.disjoint_left.mpr (fun _ hx hfront => hx.2 (hFU hfront))
  obtain ⟨qH, hqH, hqvalue⟩ := b.exists_finitePL_collar_level_parameter
    he.compatible L hL c hc hi ⟨hε.le, hε1⟩
  obtain ⟨h, hh, _, hnorm, _⟩ := exists_unitCube_inward_finitePL_collar
  obtain ⟨β, A, _, hA, hβval, hAβ, hAmem⟩ :=
    exists_finitePL_cube_collar_inner_extension h hh hnorm
  obtain ⟨f0, h0, hi0, him0, _, h0value⟩ := b.exists_inner_cube_map β A hA hAβ hAmem
  obtain ⟨f1, h1, hi1, him1, h1value⟩ :=
    exists_original_collar_shell_map L c hc hi qH hqH h hh hε hε1
  obtain ⟨h1inner, h1outer⟩ :=
    original_collar_shell_boundary L c hi hproper qH h hnorm hε hε1 f1 h1value
  have hagree : EqOn f0 f1 Q0 := by
    intro x hx
    let z : Q := β.symm ⟨x, hx⟩
    have hβx : (β z : V3) = x := congrArg Subtype.val (β.apply_symm_apply ⟨x, hx⟩)
    calc
      f0 x = f0 (β z) := congrArg f0 hβx.symm
      _ = b.map z := h0value z
      _ = c ((qH z : E), ε) := (hqvalue z).symm
      _ = f1 (β z) := by
        rw [hβval z, h1value]
        change c ((qH z : E), ε) = c ((qH z : E), 8 * ε * (1 / 8))
        rw [show 8 * ε * (1 / 8 : ℝ) = ε by ring]
      _ = f1 x := congrArg f1 hβx
  obtain ⟨_, ⟨J, hJ, hJT, _⟩, _⟩ := hh.symm
  exact exists_chartwisePLBall_of_cube_shell he.cover he.compatible J hJ hJT
    hcover hoverlap hCfront f0 f1 h0 h1 hi0 hi1 him0 him1 h1inner h1outer hagree

end PoincareConjecture.M76
