import { useState } from 'react';
import { useAuth } from '@clerk/clerk-react';

export function useInviteCode() {
    const [inviteCode, setInviteCode] = useState("");
    const [isSubmitting, setIsSubmitting] = useState(false);
    const [submitError, setSubmitError] = useState<string | null>(null);
    const { getToken } = useAuth();

    const handleSubmit = async () => {
        if (!inviteCode.trim()) return;

        setIsSubmitting(true);
        setSubmitError(null);

        try {
            const token = await getToken();
            const response = await fetch(`${import.meta.env.VITE_BACKEND_API_URL}/api/v1/invite/redeem`, {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'Authorization': `Bearer ${token}`,
                },
                body: JSON.stringify({ inviteCode }),
            });

            if (!response.ok) {
                const errorData = await response.json().catch(() => ({}));
                throw new Error(errorData.message || `Failed to redeem invite code: ${response.status}`);
            }
        } catch (err) {
            setSubmitError(err instanceof Error ? err.message : 'Failed to verify invite code');
        } finally {
            setIsSubmitting(false);
        }
    };

    return {
        value: inviteCode,
        onChange: (e: React.ChangeEvent<HTMLInputElement>) => setInviteCode(e.target.value),
        onSubmit: handleSubmit,
        error: submitError,
        isLoading: isSubmitting,

    };
}
