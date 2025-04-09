import { useAuth, useUser } from "@clerk/clerk-react";
import { Navigate } from "react-router-dom";
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Loader2 } from "lucide-react";
import { useOnboarding } from "@/hooks/useOnboarding";
import { useInviteCode } from "@/hooks/useInviteCode";
import { Input } from "@/components/ui/input";
import { LoadingScreen } from "@/components/LoadingScreen";
import { UserButton } from "@/components/UserButton";

export function InvitationPage() {
    const { isLoaded: isAuthLoaded, isSignedIn } = useAuth();
    const { user } = useUser();
    const { isLoading: isCheckingStatus, isWaitlisted, error } = useOnboarding();
    const { value, onChange, onSubmit, error: inviteError, isLoading } = useInviteCode();
    const isDisabled = !value.trim() || isLoading;

    if (!isAuthLoaded || isCheckingStatus) {
        return <LoadingScreen />;
    }

    if (!isSignedIn) {
        return <Navigate to="/sign-in" replace />;
    }

    if (error) {
        return (
            <div className="min-h-screen w-full flex items-center justify-center bg-background">
                <Card className="w-full max-w-md">
                    <CardHeader>
                        <CardTitle>Error</CardTitle>
                        <CardDescription>
                            Failed to check access status. Please try again later.
                        </CardDescription>
                    </CardHeader>
                </Card>
            </div>
        );
    }

    // Redirect to main app if user is not waitlisted
    if (!isWaitlisted) {
        return <Navigate to="/" replace />;
    }

    return (
        <div className="min-h-screen w-full flex flex-col bg-background">
            <div className="flex justify-end p-4 border-b border-border/50 bg-card">
                <UserButton />
            </div>
            <div className="flex-1 flex items-center justify-center">
                <Card className="w-full max-w-md">
                    <CardHeader>
                        <CardTitle>Access Required</CardTitle>
                        <CardDescription>
                            You're currently on our waitlist. Enter your invite code to gain access.
                        </CardDescription>
                    </CardHeader>
                    <CardContent className="space-y-4">
                        <div className="space-y-2">
                            <p className="text-sm text-muted-foreground">
                                Your email ({user?.primaryEmailAddress?.emailAddress}) is currently waitlisted.
                                If you have an invite code, please enter it below.
                            </p>
                            {inviteError && (
                                <p className="text-sm text-destructive">{inviteError}</p>
                            )}
                            <div className="flex gap-2">
                                <Input
                                    placeholder="Enter invite code"
                                    value={value}
                                    onChange={onChange}
                                    disabled={isLoading}
                                />
                                <Button
                                    onClick={onSubmit}
                                    disabled={isDisabled}
                                >
                                    {isLoading ? (
                                        <Loader2 className="h-4 w-4 animate-spin" />
                                    ) : (
                                        'Submit'
                                    )}
                                </Button>
                            </div>
                        </div>
                    </CardContent>
                </Card>
            </div>
        </div>
    );
} 