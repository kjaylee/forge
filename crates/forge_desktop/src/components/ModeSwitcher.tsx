import React from 'react';
import { useForgeStore } from '@/stores/ForgeStore';
import { Button } from "@/components/ui/button";
import { Card, CardContent } from "@/components/ui/card";
import { Separator } from "@/components/ui/separator";
import { useTheme } from 'next-themes';
import { Moon, Sun } from 'lucide-react';

const ModeSwitcher: React.FC = () => {
  const { mode, changeMode } = useForgeStore();
  const { theme, setTheme } = useTheme();

  const handleModeChange = (newMode: 'Act' | 'Plan' | 'Help') => {
    changeMode(newMode);
  };

  const toggleTheme = () => {
    setTheme(theme === 'dark' ? 'light' : 'dark');
  };

  return (
    <Card className="rounded-none border-t-0 border-x-0 shadow-none bg-muted/30">
      <CardContent className="flex items-center justify-between px-4 py-2 gap-4">
        <div className="flex space-x-1.5">
          <Button
            variant={mode.mode === 'Act' ? 'default' : 'secondary'}
            size="sm"
            onClick={() => handleModeChange('Act')}
            className="font-medium transition-all"
          >
            Act
          </Button>
          <Button
            variant={mode.mode === 'Plan' ? 'default' : 'secondary'}
            size="sm"
            onClick={() => handleModeChange('Plan')}
            className="font-medium transition-all"
          >
            Plan
          </Button>
          <Button
            variant={mode.mode === 'Help' ? 'default' : 'secondary'}
            size="sm"
            onClick={() => handleModeChange('Help')}
            className="font-medium transition-all"
          >
            Help
          </Button>
        </div>
        
        <Separator orientation="vertical" className="h-6" />
        
        <div className="flex-1 max-w-md flex items-center justify-between gap-2">
          <Card className="bg-background/60 border flex-1">
            <CardContent className="py-1.5 px-3 text-sm text-muted-foreground">
              <span className="line-clamp-1">
                {mode.description}
              </span>
            </CardContent>
          </Card>
          <Button
            variant="outline"
            size="icon"
            onClick={toggleTheme}
            className="h-8 w-8"
            title={theme === 'dark' ? 'Switch to light mode' : 'Switch to dark mode'}
          >
            {theme === 'dark' ? (
              <Sun size={16} className="text-yellow-400" />
            ) : (
              <Moon size={16} className="text-slate-700" />
            )}
          </Button>
        </div>
      </CardContent>
    </Card>
  );
};

export default ModeSwitcher;