import PoincareConjecture.Proofs.M76.Wall.Mathlib.OriginalCarrierNeighborhood
import PoincareConjecture.Proofs.M76.Wall.Mathlib.EmbeddedNonvertexHeight











set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex







theorem exists_original_carrier_height_chart
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set X} (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (T B : SimplicialComplex ℝ E) (hTK : T ≤ K) (hBT : B ≤ T)
    (x : K.space) (hxB : (x : E) ∈ B.space)
    {O : Set K.space} (hO : IsOpen O) (hxO : x ∈ O)
    (hOT : Subtype.val '' O ⊆ T.space)
    (G : OpenPartialHomeomorph X V)
    (hsource : MapsTo (fun z => (g z : X)) T.space G.source)
    (hinside : G.source ⊆ interior C)
    (hcoord : T.AffineOnFaces (fun z => G (g z)))
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V)
    {f : E → ℝ} (hf : T.AffineOnFaces f)
    (hreg : ∀ v ∈ T.vertices, f v ≠ f x)
    (psi : V →ᴬ[ℝ] ℝ)
    (hpsi : ∀ z ∈ B.space, psi (G (g z)) = psi (G (g x))) :
    ∃ (b : V →ᴬ[ℝ] ℝ) (w : V) (Q : OpenPartialHomeomorph X V),
      b.contLinear w = 1 ∧ psi.contLinear w = 0 ∧
      (g x : X) ∈ Q.source ∧ Q (g x) = G (g x) ∧ b (Q (g x)) = 0 ∧
      Q.source ⊆ G.source ∩ interior C ∧ MapsTo F Q.source T.space ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V) ∧
      (∀ y ∈ Q.source, b (Q y) = f (F y) - f x) ∧
      (∀ y ∈ Q.source, psi (Q y) = psi (G y)) ∧
      ∀ z ∈ Q.target, psi (G (Q.symm z)) = psi z := by
  have hTKs : T.space ⊆ K.space := space_subset_of_le hTK
  have hxT : (x : E) ∈ T.space := space_subset_of_le hBT hxB
  obtain ⟨hinj, _, hximage⟩ :=
    K.exists_original_open_neighborhood_of_carrier_neighborhood H g hg hTKs x
      hO hxO hOT (hinside (hsource hxT)) G hsource
  obtain ⟨ell, w, P, hellw, hpsiw, hxP, hPx, hPs, _, hPPL,
    hheight, hPpsi, hPinv⟩ :=
    hcoord.exists_embedded_nonvertex_height_chart (hK.subset hTK) hinj hf hxT
      hximage hreg B hBT hxB psi hpsi
  let b := ell - ContinuousAffineMap.const ℝ V (f x)
  let Q := G.trans P
  have hbw : b.contLinear w = 1 := by
    simpa only [b, ContinuousAffineMap.sub_contLinear,
      ContinuousAffineMap.const_contLinear, sub_zero] using hellw
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    have hgz : g z = H.symm ⟨z, hz⟩ := Subtype.ext (hg ⟨z, hz⟩)
    have hHgz : H (g z) = ⟨z, hz⟩ := by rw [hgz, H.apply_symm_apply]
    exact (hHF (g z)).symm.trans (congrArg Subtype.val hHgz)
  have hQcarrier (y : X) (hy : y ∈ Q.source) :
      F y ∈ T.space ∧ (g (F y) : X) = y := by
    obtain ⟨z, hz, hzG⟩ := interior_subset (hPs hy.2)
    have hzy : (g z : X) = y := G.injOn (hsource hz) hy.1 hzG
    have hFy : F y = z := (congrArg F hzy.symm).trans (hFg z (hTKs hz))
    refine ⟨hFy.symm ▸ hz, ?_⟩
    exact (congrArg (fun v => (g v : X)) hFy).trans hzy
  have hQx : Q (g x) = G (g x) := hPx
  have hbx : b (Q (g x)) = 0 := by
    have hellx : ell (G (g x)) = f x := by
      simpa only [hPx] using hheight x hxT hxP
    change ell (Q (g x)) - f x = 0
    rw [hQx, hellx, sub_self]
  refine ⟨b, w, Q, hbw, hpsiw, ⟨hsource hxT, hxP⟩, hQx, hbx,
    (fun y hy => ⟨hy.1, hinside hy.1⟩), (fun y hy => (hQcarrier y hy).1),
    ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [Q, ← OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V).trans (hcompat i) hPPL
  · intro y hy
    obtain ⟨hyT, hgy⟩ := hQcarrier y hy
    have hyP : G (g (F y)) ∈ P.source := by
      rw [hgy]
      exact hy.2
    have hh := hheight (F y) hyT hyP
    rw [hgy] at hh
    change ell (P (G y)) - f x = f (F y) - f x
    rw [hh]
  · intro y _
    exact hPpsi (G y)
  · intro z hz
    change psi (G (G.symm (P.symm z))) = psi z
    rw [G.right_inv hz.2]
    exact hPinv z

end Geometry.SimplicialComplex
