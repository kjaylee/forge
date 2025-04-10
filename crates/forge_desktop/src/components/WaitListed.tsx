import { useOnboarding } from "@/hooks/useOnboarding";
import { LoadingScreen } from "./LoadingScreen";
import { Navigate } from "react-router-dom";

interface WaitListedProps {
    children: React.ReactNode;
}

export function WaitListed({ children }: WaitListedProps) {
    const { isLoading, isWaitlisted } = useOnboarding();

    if (isLoading) {
        return <LoadingScreen />;
    }

    if (!isWaitlisted) {
        return <>{children}</>;
    }

    return <Navigate to="/invitation" replace />;
}
