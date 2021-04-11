import computational_complexity.cost_model
import crypto_foundations.dist_sem

open_locale big_operators

variables (G : Type) [group G] 

def diffie_hellman_candidate := G × G × G → G

def diffie_hellman_solution (f : diffie_hellman_candidate G) := 
∀ (x y : ℕ) (g : G), f (g, (g ^ x), (g ^ y)) = g ^ (x * y)

def decisional_diffie_hellman_candidate := G × G × G × G → Prop

def decisional_diffie_hellman_solution (f : decisional_diffie_hellman_candidate G) :=
∀ (x y : ℕ) (g g' : G), f (g, (g ^ x), (g ^ y), g') = (g' = g ^ (x * y)) 

/-- polylogarithmic reduction from inverse generation to inverse identification -/
example {G : ℕ → Type} [∀ n, group (G n)] 
  (group_eq_efficient : log_poly_time_cost (λ n, (λ g, g.fst = g.snd : G n × G n → Prop)))
  : log_poly_time_reducible
      (λ n, (λ g g', g' = g⁻¹ : G n → G n → Prop)) 
      (λ n, (λ gs p, p = (gs.snd = gs.fst⁻¹) : (G n × G n) → Prop → Prop)) :=
begin
  rintro ⟨f, hf, hf'⟩,
  refine ⟨λ n, (λ gs, (λ gs, gs.fst = gs.snd : G n × G n → Prop) (f gs.fst, gs.snd)), _, _⟩,
  { obtain ⟨p, hp⟩ := hf,
    obtain ⟨q, hq⟩ := group_eq_efficient,
    refine ⟨p + q, log_poly_growth_add hp.1 hq.1, λ n, _⟩,
    replace hp := hp.2 n, replace hq := hq.2 n,
    have : has_cost (λ (gs : G n × G n), (f gs.1, id gs.2)) (p ↑n) :=
      has_cost.has_cost_pair_le (by linarith) hp has_cost.has_cost_id,
    refine has_cost.has_cost_ext (has_cost.has_cost_comp this hq) (λ x, _),
    simp },
  { intros n c,
    simp [hf'],
    refine ⟨symm, symm⟩ }
end

-- theorem decisional_diffie_hellman_easier {G : ℕ → Type} [∀ n, group (G n)] 
--   (group_eq_efficient : log_poly_time_cost (λ n, (λ g g', g = g' : G n → G n → Prop)))
--   :
--   log_poly_time_reducible 
--     (λ n, diffie_hellman_candidate (G n)) 
--     (λ n, decisional_diffie_hellman_candidate (G n))
--     (λ n, diffie_hellman_solution (G n)) 
--     (λ n, decisional_diffie_hellman_solution (G n)):=
-- begin
--   simp [log_poly_time_reducible],
--   refine ⟨λ n, (λ f, (λ g gx gy g', f g gx gy = g')), _, _⟩,
--   {
--     obtain ⟨p, hp, h⟩ := group_eq_efficient,
--     refine ⟨p, hp, _⟩,
--     intro n,
--     specialize h n,
    
  
--   }
-- end