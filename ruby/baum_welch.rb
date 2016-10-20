class BaumWelch
  def initialize
  end

  def baum_welch_step(trans, emiss, init, observation_sequences)
    hmm = HMM.new(trans, emiss, init).forward_backward
    fb_results = observation_sequences.map { |os| hmm.forward_backward os }

    {updated_initial_probs: updated_initial_probs(init, fb_results),
     updated_transition: updated_transition(observation_sequences, fb_results),
     updated_emission: updated_emission(observation_sequences, fb_results)
    }
  end

  private

  def updated_initial_probs(initial_probs, fb_results)
    len = fb_results.length
    fb_results.map do |fb_result|
      fb_result[0].map { |x| x / len }
    end.inject :vector_add
  end

  def updated_transition(observation_sequences, fb_results)
    denominator = [0.0] * num_states
    (0...num_states).each do |state|
      observation_sequences.each_with_index do |seq, seq_index|
        seq[0..-2].each_with_index do |obs, obs_index|
          denominator[state] += fb_results[seq_index][obs_index][state]
        end
      end
    end

    numerator = (0...num_states).map { [0.0] * num_states }
    (0...num_states).each do |i|
      (0...num_states).each do |j|
        observation_sequences.each_with_index do |seq, seq_index|
          seq[0..-2].each_with_index do |obs, obs_index|
            # p(z_t = i, z_t+1 = j | o_1:k) = p(z_t+1=j|z_t=i) * p(z_t=i | o_1:k)
            numerator[i][j] += transition[i][j] * fb_results[seq_index][obs_index][i]
          end
        end
      end
    end

    result = (0...num_states).map { [0.0] * num_states }
    (0...num_states).each do |i|
      (0...num_states).each do |j|
        result[i][j] = numerator[i][j] / denominator[i]
      end
    end

    result
  end

  # emission : [state] -> [observation] -> prob
  def updated_emission(observation_sequences, fb_results)
    denominator_for_state = [0.0]*num_states

    (0...observation_sequences.length).each do |seq_index|
      (0...observation_sequences[seq_index].length).each do |obs_index|
        (0...num_states).each do |state|
          denominator_for_state[state] += fb_results[seq_index][obs_index][state]
        end
      end
    end

    # assumes all observation sequences have same length
    numerator_for_state_and_obs = (0...num_states).map { [0.0]*observation_sequences.first.length }
    observation_sequences.each_with_index do |seq, seq_index|
      seq.each_with_index do |obs, obs_index|
        (0...num_states).each do |state|
          numerator_for_state_and_obs[state][obs] += fb_results[seq_index][obs_index][state]
        end
      end
    end

    numerator_for_state_and_obs.with_index.map do |numerator, state|
      numerator.map { |x| x / denominator_for_state[state] }
    end
  end

  def vector_add(v1, v2)
    v1.map.with_index { |x, i| x + v2[i] }
  end
end
